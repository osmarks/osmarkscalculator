#![feature(float_next_up_down)]

use anyhow::{Result, Context, bail};
use inlinable_string::InlinableString;
use interval_arithmetic::Interval;
use std::{collections::HashMap, convert::TryInto};
use std::borrow::Cow;
use std::sync::Arc;
#[cfg(target_family="wasm")]
use wasm_bindgen::prelude::*;

#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

mod parse;
mod value;
mod util;
mod env;
mod interval_arithmetic;

use value::Value;
use env::{Rule, Ruleset, Env, Bindings, RuleResult, Operation};

// Main pattern matcher function; 
fn match_and_bind(expr: &Value, rule: &Rule, env: &Env) -> Result<Option<Value>> {
    fn go(expr: &Value, cond: &Value, env: &Env, already_bound: &Bindings) -> Result<Option<Bindings>> {
        match (expr, cond) {
            // numbers match themselves
            (Value::Num(a), Value::Num(b)) => if a == b { Ok(Some(HashMap::new())) } else { Ok(None) },
            (Value::ExactNum(a), Value::ExactNum(b)) => if a == b { Ok(Some(HashMap::new())) } else { Ok(None) },
            // handle predicated value - check all predicates, succeed with binding if they match
            (val, Value::Call(x, args)) if x == "#" => {
                let preds = &args[1..];
                let (mut success, mut bindings) = match go(val, &args[0], env, already_bound)? {
                    Some(bindings) => (true, bindings),
                    None => (false, already_bound.clone())
                };

                for pred in preds {
                    match pred {
                        // "Num" predicate matches successfully if something is a number
                        Value::Identifier(i) if i.as_ref() == "Num" => {
                            match val {
                                Value::Num(_) | Value::ExactNum(_) => (),
                                _ => success = false
                            }
                        },
                        // "Ident" does the same for idents
                        Value::Identifier(i) if i.as_ref() == "Ident" => {
                            match val {
                                Value::Identifier(_) => (),
                                _ => success = false
                            }
                        },
                        // Invert match success
                        Value::Identifier(i) if i.as_ref() == "Not" => {
                            success = !success
                        },
                        Value::Call(head, args) if head.as_ref() == "And" => {
                            // Try all patterns it's given, and if any fails then fail the match
                            for arg in args.iter() {
                                match go(val, arg, env, &bindings)? {
                                    Some(new_bindings) => bindings.extend(new_bindings),
                                    None => success = false
                                }
                            }
                        },
                        Value::Call(head, args) if head.as_ref() == "Eq" => {
                            // Evaluate all arguments and check if they are equal
                            let mut compare_against = None;
                            for arg in args.iter() {
                                let mut evaluated_value = arg.subst(&bindings);
                                run_rewrite(&mut evaluated_value, env).context("evaluating Eq predicate")?;
                                match compare_against {
                                    Some(ref x) => if x != &evaluated_value {
                                        success = false
                                    },
                                    None => compare_against = Some(evaluated_value)
                                }
                            }
                        },
                        Value::Call(head, args) if head.as_ref() == "Gte" => {
                            // Evaluate all arguments and do comparison.
                            let mut x = args[0].subst(&bindings);
                            let mut y = args[1].subst(&bindings);
                            run_rewrite(&mut x, env).context("evaluating Gte predicate")?;
                            run_rewrite(&mut y, env).context("evaluating Gte predicate")?;
                            success &= x >= y;
                        },
                        Value::Call(head, args) if head.as_ref() == "Or" => {
                            // Tries all patterns it's given and will set the match to successful if *any* of them works
                            for arg in args.iter() {
                                match go(val, arg, env, &bindings)? {
                                    Some(new_bindings) => {
                                        bindings.extend(new_bindings);
                                        success = true
                                    },
                                    None => ()
                                }
                            }
                        },
                        _ => bail!("invalid predicate {:?}", pred)
                    }
                }
                Ok(match success {
                    true => Some(bindings),
                    false => None
                })
            },
            (Value::Call(exp_head, exp_args), Value::Call(rule_head, rule_args)) => {
                let mut exp_args = Cow::Borrowed(exp_args);
                // Regardless of any special casing for associativity etc., different heads mean rules can never match
                if exp_head != rule_head { return Ok(None) }

                let op = env.get_op(exp_head);
    
                // Copy bindings from the upper-level matching, so that things like "a+(b+a)" work.
                let mut out_bindings = already_bound.clone();

                // Special case for associative expressions: split off extra arguments into a new tree
                if op.associative && rule_args.len() < exp_args.len() {
                    let exp_args = exp_args.to_mut();
                    let rest = exp_args.split_off(rule_args.len() - 1);
                    let rem = Value::Call(exp_head.clone(), rest);
                    exp_args.push(rem);
                }
                if rule_args.len() != exp_args.len() { return Ok(None) }
    
                // Try and match all "adjacent" arguments to each other
                for (rule_arg, exp_arg) in rule_args.iter().zip(&*exp_args) {
                    match go(exp_arg, rule_arg, env, &out_bindings)? {
                        Some(x) => out_bindings.extend(x),
                        None => return Ok(None)
                    }
                }
                Ok(Some(out_bindings))
            },
            // identifier pattern matches anything, unless the identifier has already been bound to something else
            (x, Value::Identifier(a)) => {
                if let Some(b) = already_bound.get(a) {
                    if b != x {
                        return Ok(None);
                    }
                };
                Ok(Some(vec![(a.clone(), x.clone())].into_iter().collect()))
            },
            // anything else doesn't match
            _ => Ok(None)
        }
    }
    // special case at top level of expression - try to match pattern to different subranges of input
    match (expr, &rule.condition) {
        // this only applies to matching one "call" against a "call" pattern (with same head)
        (Value::Call(ehead, eargs), Value::Call(rhead, rargs)) => {
            // and also only to associative operations
            if env.get_op(ehead).associative && eargs.len() > rargs.len() && ehead == rhead {
                // consider all possible subranges of the arguments of the appropriate length
                for range_start in 0..=(eargs.len() - rargs.len()) {
                    // extract the arguments & convert into new Value
                    let c_args = eargs[range_start..range_start + rargs.len()].iter().cloned().collect();
                    let c_call = Value::Call(ehead.clone(), c_args);
                    // attempt to match the new subrange against the current rule
                    if let Some(r) = match_and_bind(&c_call, rule, env)? {
                        // generate new output with result
                        let mut new_args = Vec::with_capacity(3);
                        // add back extra start items
                        if range_start != 0 {
                            new_args.push(Value::Call(ehead.clone(), eargs[0..range_start].iter().cloned().collect()))
                        }
                        new_args.push(r);
                        // add back extra end items
                        if range_start + rargs.len() != eargs.len() {
                            new_args.push(Value::Call(ehead.clone(), eargs[range_start + rargs.len()..eargs.len()].iter().cloned().collect()))
                        }
                        let new_exp = Value::Call(ehead.clone(), new_args);
                        return Ok(Some(new_exp))
                    }
                }
            }
        }
        _ => ()
    }
    // substitute bindings from matching into either an intrinsic or the output of the rule
    if let Some(bindings) = go(expr, &rule.condition, env, &HashMap::new())? {
        Ok(Some(match &rule.result {
            RuleResult::Intrinsic(id) => (env.intrinsics)(*id, &bindings).with_context(|| format!("applying intrinsic {}", id))?,
            RuleResult::Exp(e) => e.subst(&bindings)
        }))
    } else {
        Ok(None)
    }
}

// Sort any commutative expressions
fn canonical_sort(v: &mut Value, env: &Env) -> Result<()> {
    match v {
        Value::Call(head, args) => if env.get_op(head).commutative {
            args.sort_by(|a, b| a.partial_cmp(b).unwrap());
        },
        _ => ()
    }
    Ok(())
}

// Associative expression flattening.
fn flatten_tree(v: &mut Value, env: &Env) -> Result<()> {
    match v {
        Value::Call(head, args) => {
            if env.get_op(head).associative {
                // Not the most efficient algorithm, but does work.
                // Repeatedly find the position of a flatten-able child node, and splice it into the argument list.
                loop {
                    let mut move_pos = None;
                    for (i, child) in args.iter().enumerate() {
                        if let Some(child_head) = child.head() {
                            if *head == child_head {
                                move_pos = Some(i)
                            }
                        }
                    }
                    match move_pos {
                        Some(pos) => {
                            let removed = std::mem::replace(&mut args[pos], Value::Identifier(InlinableString::from("")));
                            // We know that removed will be a Call (because its head wasn't None earlier). Unfortunately, rustc does not know this.
                            match removed {
                                Value::Call(_, removed_child_args) => args.splice(pos..=pos, removed_child_args.into_iter()),
                                _ => unreachable!()
                            };
                        },
                        None => break
                    }
                }
            }
            /*
            for child in args.iter_mut() {
                flatten_tree(child, env)?;
            }
            */
            // Also do sorting after flattening, to avoid any weirdness with ordering.
            canonical_sort(v, env)?;
            return Ok(())
        },
        _ => return Ok(())
    }
}

// Applies rewrite rulesets to an expression.
fn run_rewrite(v: &mut Value, env: &Env) -> Result<()> {
    loop {
        // Compare original and final hash instead of storing a copy of the original value and checking equality
        // Collision probability is negligible and this is substantially faster than storing/comparing copies.
        let original_hash = v.get_hash();
        
        flatten_tree(v, env).context("flattening tree")?;
        // Call expressions can be rewritten using pattern matching rules; identifiers can be substituted for bindings if available
        match v {
            Value::Call(head, args) => {
                let head = head.clone();
                
                // Rewrite sub-expressions using existing environment
                args.iter_mut().try_for_each(|arg| run_rewrite(arg, env).with_context(|| format!("rewriting {}", arg.render_to_string(env))))?;
                
                // Try to apply all applicable rules from all rulesets, in sequence
                for ruleset in env.ruleset.iter() {
                    if let Some(rules) = ruleset.get(&head) {
                        // Within a ruleset, rules are applied backward. This is nicer for users using the program interactively.
                        for rule in rules.iter().rev() {
                            if let Some(result) = match_and_bind(v, rule, env).with_context(|| format!("applying rule {} -> {:?}", rule.condition.render_to_string(env), rule.result))? {
                                *v = result;
                                flatten_tree(v, env).context("flattening tree after rule application")?;
                            }
                        }
                    }
                }
            },
            // Substitute in bindings which have been provided
            Value::Identifier(ident) => {
                match env.bindings.get(ident) {
                    Some(val) => {
                        *v = val.clone();
                    },
                    None => return Ok(())
                }
            },
            _ => {
                return Ok(())
            }
        }
        if original_hash == v.get_hash() {
            break
        }
    }
    Ok(())
}

// Utility function for defining intrinsic functions for binary operators.
// Converts a function which does the actual operation to a function from bindings to a value.
fn wrap_binop<F: 'static + Fn(Interval, Interval) -> Result<Interval> + Sync + Send, G: 'static + Fn(i128, i128) -> Result<i128> + Sync + Send>(op: F, op_exact: G) -> Box<dyn Fn(&Bindings) -> Result<Value> + Sync + Send> {
    Box::new(move |bindings: &Bindings| {
        let a = bindings.get(&InlinableString::from("a")).context("binop missing first argument")?;
        let b = bindings.get(&InlinableString::from("b")).context("binop missing second argument")?;
        match (a, b) {
            (Value::ExactNum(a), Value::ExactNum(b)) => op_exact(*a, *b).map(Value::ExactNum),
            _ => op(a.assert_num("binop first argument")?, b.assert_num("binop second argument")?).map(Value::Num)
        }
    })
}

fn wrap_binop_no_exact<F: 'static + Fn(Interval, Interval) -> Result<Interval> + Sync + Send>(op: F) -> Box<dyn Fn(&Bindings) -> Result<Value> + Sync + Send> {
    Box::new(move |bindings: &Bindings| {
        let a = bindings.get(&InlinableString::from("a")).context("binop missing first argument")?;
        let b = bindings.get(&InlinableString::from("b")).context("binop missing second argument")?;
        op(a.assert_num("binop first argument")?, b.assert_num("binop second argument")?).map(Value::Num)
    })
}

fn run_intrinsic(id: usize, args: &HashMap<InlinableString, Value>) -> Result<Value> {
    match id {
        0 => wrap_binop(|a, b| Ok(a + b), |a, b| Ok(a + b))(args),
        1 => wrap_binop(|a, b| Ok(a - b), |a, b| Ok(a - b))(args),
        2 => wrap_binop(|a, b| Ok(a * b), |a, b| Ok(a * b))(args),
        3 => wrap_binop_no_exact(|a, b| Ok(a / b))(args),
        4 => wrap_binop(|a, b| a.pow(b), |a, b| a.checked_pow(b.try_into()?).context("integer overflow"))(args),
        5 => {
            // Substitute a single, given binding var=value into a target expression
            let var = args.get(&InlinableString::from("var")).unwrap();
            let value = args.get(&InlinableString::from("value")).unwrap();
            let target = args.get(&InlinableString::from("target")).unwrap();
            let name = var.assert_ident("Subst")?;
            let mut new_bindings = HashMap::new();
            new_bindings.insert(name, value.clone());
            Ok(target.subst(&new_bindings))
        },
        6 => wrap_binop(|_a, _b| bail!("no modulo on floats yet"), |a, b| a.checked_rem(b).context("division by zero"))(args),
        7 => Ok(Value::ExactNum(args.get(&InlinableString::from("a")).context("round missing first argument")?.assert_num("abs")?.round_to_int())),
        8 => {
            let a = args.get(&InlinableString::from("a")).context("interval missing first argument")?;
            let b = args.get(&InlinableString::from("b")).context("interval missing second argument")?;
            Ok(Value::Num(Interval(a.assert_num("interval first argument")?.0, b.assert_num("interval second argument")?.1)))
        }
        _ => bail!("invalid intrinsic id {}", id)
    }
}

// Provides a basic environment with operator commutativity/associativity operations and intrinsics.
fn make_initial_env() -> Env {
    let mut ops = HashMap::new();
    ops.insert(InlinableString::from("+"), Operation { commutative: true, associative: true });
    ops.insert(InlinableString::from("*"), Operation { commutative: true, associative: true });
    ops.insert(InlinableString::from("-"), Operation { commutative: false, associative: false });
    ops.insert(InlinableString::from("/"), Operation { commutative: false, associative: false });
    ops.insert(InlinableString::from("^"), Operation { commutative: false, associative: false });
    ops.insert(InlinableString::from("="), Operation { commutative: false, associative: false });
    ops.insert(InlinableString::from("#"), Operation { commutative: false, associative: true });
    let ops = Arc::new(ops);
    let intrinsics = Arc::new(run_intrinsic);
    Env {
        ruleset: vec![],
        ops: ops.clone(),
        intrinsics: intrinsics.clone(),
        bindings: HashMap::new()
    }
}

pub const BUILTINS: &str = "
SetStage[all]
a#Num + b#Num = Intrinsic[0]
a#Num - b#Num = Intrinsic[1]
a#Num * b#Num = Intrinsic[2]
a#Num / b#Num = Intrinsic[3]
a#Num ^ b#Num = Intrinsic[4]
Subst[var=value, target] = Intrinsic[5]
Round[a#Num] = Intrinsic[7]
Interval[a#Num, b#Num] = Intrinsic[8]
PushRuleset[builtins]
";

pub const GENERAL_RULES: &str = "
SetStage[all]
(a*b#Num)+(a*c#Num) = (b+c)*a
Negate[a] = 0 - a
a^b*a^c = a^(b+c)
a^0 = 1
a^1 = a
(a^b)^c = a^(b*c)
0*a = 0
0+a = a
1*a = a
x/x = 1
(n*x)/x = n
PushRuleset[general_rules]
";

pub const NORMALIZATION_RULES: &str = "
SetStage[norm]
a/b = a*b^Negate[1]
a+b#Num*a = (b+1)*a
a^b#Num#Gte[b, 2] = a*a^(b-1)
a-c#Num*b = a+Negate[c]*b
a+a = 2*a
a*(b+c) = a*b+a*c
a-b = a+Negate[1]*b
PushRuleset[normalization]
";

pub const DENORMALIZATION_RULES: &str = "
SetStage[denorm]
a*a = a^2
a^b#Num*a = a^(b+1)
c+a*b#Num#Gte[0, b] = c-a*Negate[b]
PushRuleset[denormalization]
";

pub const DIFFERENTIATION_DEFINITION: &str = "
SetStage[all]
D[x, x] = 1
D[a#Num, x] = 0
D[f+g, x] = D[f, x] + D[g, x]
D[f*g, x] = D[f, x] * g + D[g, x] * f
D[a#Num*f, x] = a * D[f, x]
PushRuleset[differentiation]
";

pub const FACTOR_DEFINITION: &str = "
SetStage[post_norm]
Factor[x, a*x+b] = x * (a + Factor[x, b] / x)
PushRuleset[factor]
SetStage[pre_denorm]
Factor[x, a] = a
PushRuleset[factor_postprocess]
SetStage[denorm]
x^n/x = x^(n-1)
(a*x^n)/x = a*x^(n-1)
PushRuleset[factor_postpostprocess]
";

pub struct ImperativeCtx {
    bindings: Bindings,
    current_ruleset_stage: InlinableString,
    current_ruleset: Ruleset,
    rulesets: HashMap<InlinableString, Arc<Ruleset>>,
    stages: Vec<(InlinableString, Vec<InlinableString>)>,
    pub base_env: Env
}

impl ImperativeCtx {
    // Make a new imperative context
    // Stages are currently hardcoded, as adding a way to manage them would add lots of complexity
    // for limited benefit
    pub fn init() -> Self {
        let stages = [
            "pre_norm",
            "norm",
            "post_norm",
            "pre_denorm",
            "denorm",
            "post_denorm"
        ].iter().map(|name| (InlinableString::from(*name), vec![])).collect();
        ImperativeCtx {
            bindings: HashMap::new(),
            current_ruleset_stage: InlinableString::from("post_norm"),
            current_ruleset: HashMap::new(),
            rulesets: HashMap::new(),
            stages,
            base_env: make_initial_env()
        }
    }

    // Insert a rule into the current ruleset; handles switching out the result for a relevant intrinsic use, generating possible reorderings, and inserting into the lookup map.
    fn insert_rule(&mut self, condition: &Value, result_val: Value) -> Result<()> {
        let result = match result_val {
            Value::Call(head, args) if head == "Intrinsic" => RuleResult::Intrinsic(args[0].assert_num("Intrinsic ID")?.round_to_int() as usize),
            _ => RuleResult::Exp(result_val)
        };
        for rearrangement in condition.pattern_reorderings(&self.base_env).into_iter() {
            let rule = Rule {
                condition: rearrangement,
                result: result.clone()
            };
            self.current_ruleset.entry(condition.head().unwrap()).or_insert_with(Vec::new).push(rule);
        }
        Ok(())
    }

    // Run a single statement (roughly, a line of user input) on the current context
    fn eval_statement(&mut self, mut stmt: Value) -> Result<Option<Value>> {
        match stmt {
            // = sets a binding or generates a new rule.
            Value::Call(head, args) if head.as_ref() == "=" => {
                match &args[0] {
                    // Create a binding if the LHS (left hand side) is just an identifier
                    Value::Identifier(id) => {
                        let rhs = self.eval_statement(args[1].clone())?;
                        if let Some(val) = rhs.clone() {
                            self.bindings.insert(id.clone(), val);
                        }
                        Ok(rhs)
                    },
                    // If the LHS is a call, then a rule should be created instead.
                    Value::Call(_head, _args) => {
                        let rhs = self.eval_statement(args[1].clone())?;
                        if let Some(val) = rhs.clone() {
                            self.insert_rule(&args[0], val)?;
                        }
                        Ok(rhs)
                    },
                    // Rebinding numbers can only bring confusion, so it is not allowed.
                    // They also do not have a head, and so cannot be inserted into the ruleset anyway.
                    Value::Num(_) | Value::ExactNum(_) => bail!("You cannot rebind numbers")
                }
            },
            // SetStage[] calls set the stage the current ruleset will be applied at
            Value::Call(head, args) if head.as_ref() == "SetStage" => {
                let stage = args[0].assert_ident("SetStage requires an identifier for stage")?;
                if stage != "all" && None == self.stages.iter().position(|s| s.0 == stage) {
                    bail!("No such stage {}", stage);
                }
                self.current_ruleset_stage = stage;
                Ok(None)
            },
            // Move the current ruleset from the "buffer" into the actual list of rules to be applied at each stage
            Value::Call(head, args) if head.as_ref() == "PushRuleset" => {
                let name = args[0].assert_ident("PushRuleset requires an identifier for ruleset name")?;
                // Get ruleset and set the current one to empty
                let ruleset = std::mem::replace(&mut self.current_ruleset, HashMap::new());
                // Push ruleset to stages it specifies
                for (stage_name, stage_rulesets) in self.stages.iter_mut() {
                    if *stage_name == self.current_ruleset_stage || self.current_ruleset_stage == "all" {
                        stage_rulesets.push(name.clone());
                    }
                }
                // Insert actual ruleset data under its name
                self.rulesets.insert(name, Arc::new(ruleset));
                Ok(None)
            },
            // Anything not special should just be repeatedly run through each rewrite stage.
            _ => {
                let env = self.base_env.with_bindings(&self.bindings);
                for (stage_name, stage_rulesets) in self.stages.iter() {
                    // Add relevant rulesets to a new environment for this stage
                    let mut env = env.clone();
                    for ruleset in stage_rulesets.iter() {
                        env = env.with_ruleset(self.rulesets[ruleset].clone());
                    }
                    // Also add the current ruleset if applicable
                    if self.current_ruleset_stage == *stage_name || self.current_ruleset_stage == "all" {
                        env = env.with_ruleset(Arc::new(self.current_ruleset.clone()));
                    }
                    run_rewrite(&mut stmt, &env).with_context(|| format!("failed in {} stage", stage_name))?;
                    // If a ruleset is only meant to be applied in one particular stage, it shouldn't have any later stages applied to it, 
                    // or the transformation it's meant to do may be undone
                    if self.current_ruleset_stage == *stage_name {
                        break
                    }
                }
                Ok(Some(stmt))
            }
        }
    }

    // Evaluate an entire "program" (multiple statements delineated by ; or newlines)
    pub fn eval_program(&mut self, program: &str) -> Result<Option<Value>> {
        let mut tokens = parse::lex(program)?;
        let mut last_value = None;
        loop {
            // Split at the next break token
            let remaining_tokens = tokens.iter().position(|x| *x == parse::Token::Break).map(|ix| tokens.split_off(ix + 1));
            // Trim EOF/break tokens 
            match tokens[tokens.len() - 1] {
                parse::Token::Break | parse::Token::EOF => tokens.truncate(tokens.len() - 1),
                _ => ()
            };
            // If the statement/line isn't blank, readd EOF for the parser, parse into an AST then Value, and evaluate the statement
            if tokens.len() > 0 {
                tokens.push(parse::Token::EOF);
                let value = Value::from_ast(parse::parse(tokens)?);
                last_value = self.eval_statement(value)?;
            }
            // If there was no break after the current position, this is now done. Otherwise, move onto the new remaining tokens.
            match remaining_tokens {
                Some(t) => { tokens = t },
                None => break
            }
        }
        Ok(last_value)
    }
}

#[cfg(target_family="wasm")]
static mut JS_CONTEXT: Option<ImperativeCtx> = None;

#[cfg(target_family="wasm")]
#[wasm_bindgen]
pub fn init_context() {
    unsafe {
        JS_CONTEXT = Some(ImperativeCtx::init());
    }
}
#[cfg(target_family="wasm")]
unsafe fn load_defaults_internal() -> Result<()> {
    let ctx = (&mut JS_CONTEXT).as_mut().unwrap();
    ctx.eval_program(BUILTINS)?;
    ctx.eval_program(GENERAL_RULES)?;
    ctx.eval_program(FACTOR_DEFINITION)?;
    ctx.eval_program(DENORMALIZATION_RULES)?;
    ctx.eval_program(NORMALIZATION_RULES)?;
    ctx.eval_program(DIFFERENTIATION_DEFINITION)?;
    Ok(())
}
#[cfg(target_family="wasm")]
#[wasm_bindgen]
pub fn load_defaults() {
    unsafe {
        load_defaults_internal().unwrap();
    }
}
#[cfg(target_family="wasm")]
#[wasm_bindgen]
pub fn run_program(program: &str) -> String {
    unsafe {
        let ctx = (&mut JS_CONTEXT).as_mut().unwrap();
        match ctx.eval_program(program) {
            Ok(Some(result)) => result.render_to_string(&ctx.base_env).to_string(),
            Ok(None) => String::new(),
            Err(e) => format!("Error: {:?}", e)
        }
    }
}
#[cfg(target_family="wasm")]
#[wasm_bindgen]
pub fn deinit_context() {
    unsafe {
        std::mem::take(&mut JS_CONTEXT);
    }
}

#[cfg(test)]
mod test {
    use crate::{ImperativeCtx, BUILTINS, GENERAL_RULES, NORMALIZATION_RULES, DENORMALIZATION_RULES, DIFFERENTIATION_DEFINITION, FACTOR_DEFINITION};

    #[test]
    fn end_to_end_tests() {
        let mut ctx = ImperativeCtx::init();
        ctx.eval_program(BUILTINS).unwrap();
        ctx.eval_program(GENERAL_RULES).unwrap();
        ctx.eval_program(FACTOR_DEFINITION).unwrap();
        ctx.eval_program(DENORMALIZATION_RULES).unwrap();
        ctx.eval_program(NORMALIZATION_RULES).unwrap();
        ctx.eval_program(DIFFERENTIATION_DEFINITION).unwrap();
        let test_cases = [
            ("Factor[x, x*3+x^2]", "(3+x)*x"),
            ("x^a/x^(a+1)", "x^Negate[1]"),
            ("Negate[a+b]", "Negate[1]*b-a"),
            ("Subst[x=4, x+4+4+4+4]", "20"),
            ("(a+b)*(c+d)*(e+f)", "a*c*e+a*c*f+a*d*e+a*d*f+b*c*e+b*c*f+b*d*e+b*d*f"),
            ("Round[(12+55)^3-75+16/(2*2)+5+3*4]", "300709"),
            ("D[3*x^3 + 6*x, x] ", "6+9*x^2"),
            ("Fib[n] = Fib[n-1] + Fib[n-2] 
            Fib[0] = 0 
            Fib[1] = 1 
            Fib[6]", "8"),
            ("Subst[b=a, b+a]", "2*a"),
            ("(a+b+c)^2", "2*a*b+2*a*c+2*b*c+a^2+b^2+c^2"),
            ("a = 7
            b = Negate[4] 
            a + b", "3"),
            ("(x+2)^7", "128+2*x^6+12*x^5+12*x^6+16*x^3+16*x^5+24*x^4+24*x^5+32*x^2+32*x^3+32*x^5+128*x^2+256*x^4+448*x+512*x^2+512*x^3+x^7")
        ];
        for (input, expected_result) in test_cases {
            let lhs = ctx.eval_program(input).unwrap();
            let lhs = lhs.as_ref().unwrap().render_to_string(&ctx.base_env);
            println!("{} evaluated to {}; expected {}", input, lhs, expected_result);
            assert_eq!(lhs, expected_result);   
        }

        let error_cases = [
            ("1/0")
        ];

        for error_case in error_cases {
            if let Err(e) = ctx.eval_program(error_case) {
                println!("{} produced error {:?}", error_case, e);
            } else {
                panic!("should have errored: {}", error_case)
            }
        }

        println!("All tests passed.")
    }
}