use inlinable_string::{InlinableString, StringExt};
use std::hash::{Hash, Hasher};
use std::collections::{hash_map::DefaultHasher, HashSet, HashMap};
use std::fmt::{self, Write};
use itertools::Itertools;
use anyhow::{Result, anyhow};

use crate::parse::{Ast, precedence};
use crate::env::{Env, Bindings};
use crate::util::char_to_string;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Value {
    Num(i128),
    Call(InlinableString, Vec<Value>),
    Identifier(InlinableString),
}

impl Value {
    // Converts an AST from `parse.rs` to a Value
    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Op(char, t1, t2) => Value::Call(char_to_string(char), vec![Value::from_ast(*t1), Value::from_ast(*t2)]),
            Ast::Call(f, args) => {
                Value::Call(match *f {
                    Ast::Identifier(n) => n,
                    _ => unimplemented!()
                }, args.into_iter().map(Value::from_ast).collect())
            },
            Ast::Num(n) => Value::Num(n),
            Ast::Identifier(i) => Value::Identifier(i)
        }
    }

    // Gets the hash of a Value
    pub fn get_hash(&self) -> u64 {
        // according to https://doc.rust-lang.org/std/collections/hash_map/struct.DefaultHasher.html, all instances created here are guaranteed to be the same
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    // Gets the head (string at start of call expression)
    pub fn head(&self) -> Option<InlinableString> {
        match self {
            Value::Call(fun, _) => Some(fun.clone()),
            _ => None
        }
    }

    // Replace variables with incremental IDs, vaguely like de Bruijn indices in lambda calculus.
    // Allows patterns to be compared regardless of the names of the identifiers they contain.
    fn canonicalize_variables(&self) -> (Self, Bindings) {
        fn go(v: &Value, bindings: &mut Bindings, counter: &mut usize) -> Value {
            match v {
                Value::Num(_) => v.clone(),
                Value::Identifier(name) => {
                    match bindings.get(name) {
                        Some(id) => id.clone(),
                        None => {
                            let mut next_id = InlinableString::new();
                            write!(next_id, "{:X}", counter).unwrap();
                            let next_id = Value::Identifier(next_id);
                            *counter += 1;
                            bindings.insert(name.clone(), next_id.clone());
                            next_id
                        }
                    }
                },
                Value::Call(head, args) => {
                    Value::Call(head.clone(), args.iter().map(|x| go(x, bindings, counter)).collect())
                }
            }
        }
        let mut vars = HashMap::new();
        let mut ctr = 0;
        (go(self, &mut vars, &mut ctr), vars)
    }

    // Hash the canonical-variables form of a pattern. Allows patterns to be checked for equality safely.
    fn pattern_hash(&self) -> u64 {
        self.canonicalize_variables().0.get_hash()
    }

    // Generate all possible ways a pattern can be ordered, given commutative operators it may contain.
    // This also recurses into child nodes.
    pub fn pattern_reorderings(&self, env: &Env) -> Vec<Self> {
        // Filter out redundant patterns from a result, and convert the argument lists back into Values
        // Due to typing, this has to be factored out into a separate generic function
        // rather than being part of the main logic below.
        fn map_result<I: Iterator<Item=Vec<Value>>>(head: &InlinableString, result: I) -> Vec<Value> {
            let mut existing_patterns = HashSet::new();
            result.flat_map(|x| {
                let resulting_value = Value::Call(head.clone(), x);
                let hash = resulting_value.pattern_hash();
                if existing_patterns.contains(&hash) {
                    None
                } else {
                    existing_patterns.insert(hash);
                    Some(resulting_value)
                }
            }).collect()
        }

        match self {
            // Call expressions can have their child nodes reordered and can be reordered themselves, if the head is a commutative operator
            Value::Call(head, args) => {
                let result = args.iter()
                    // Recursive step: generate all the valid reorderings of each child node.
                    .map(|x| x.pattern_reorderings(env))
                    // Generate all possible combinations of those reorderings.
                    .multi_cartesian_product();
                // Generate all possible permutations of those combinations, if the operation allows for this.
                if env.get_op(head).commutative {
                    map_result(head, result.flat_map(|comb| {
                        let k = comb.len();
                        comb.into_iter().permutations(k)
                    }))
                } else {
                    map_result(head, result)
                }                
            },
            // Any other expression type is not reorderable.
            _ => {
                vec![self.clone()]
            }
        }
    }

    // Substitute bindings into an expression tree;
    // the main match_and_bind function can also do this, but doing it here is more efficient
    // when its full power is not needed
    pub fn subst(&self, bindings: &Bindings) -> Value {
        match self {
               Value::Identifier(name) => {
                match bindings.get(name) {
                    Some(value) => value.clone(),
                    None => Value::Identifier(name.clone())
                }
            },
            Value::Call(fun, args) => Value::Call(fun.clone(), args.iter().map(|x| x.subst(bindings)).collect()),
            x => x.clone()
        }
    }

    // Ensure that a value is a number, returning an error otherwise.
    pub fn assert_num(&self, ctx: &'static str) -> Result<i128> {
        match self {
            Value::Num(n) => Ok(*n),
            _ => Err(anyhow!("expected number, got {:?}", self).context(ctx))
        }
    }

    // The same but for identfiers.
    pub fn assert_ident(&self, ctx: &'static str) -> Result<InlinableString> {
        match self {
            Value::Identifier(i) => Ok(i.clone()),
            _ => Err(anyhow!("expected identifier, got {:?}", self).context(ctx))
        }
    }

    pub fn render<W: fmt::Write>(&self, f: &mut W, env: &Env) -> fmt::Result {
        fn go<W: fmt::Write>(v: &Value, parent_prec: Option<usize>, env: &Env, f: &mut W) -> fmt::Result {
            match v {
                // As unary - isn't parsed, negative numbers are written with Negate instead.
                Value::Num(x) => if *x >= 0 {
                    write!(f, "{}", x)
                } else { write!(f, "Negate[{}]", -x) },
                Value::Identifier(i) => write!(f, "{}", i),
                Value::Call(head, args) => {
                    match env.ops.get(head) {
                        Some(_) => {
                            // If the precedence of the enclosing operation is greater than or equal to this one's,
                            // add brackets around this one
                            let this_prec = precedence(head.chars().next().unwrap());
                            let render_brackets = match parent_prec {
                                Some(prec) => prec >= this_prec,
                                None => false
                            };
                            if render_brackets {
                                write!(f, "(")?;
                            }
                            for (i, arg) in args.iter().enumerate() {
                                go(arg, Some(this_prec), env, f)?;
                                if i + 1 != args.len() {
                                    write!(f, "{}", head)?;
                                }
                            }
                            if render_brackets {
                                write!(f, ")")?;
                            }
                        },
                        // Just write a call expression with square brackets.
                        None => {
                            write!(f, "{}[", head)?;
                            for (i, arg) in args.iter().enumerate() {
                                go(arg, None, env, f)?;
                                if i + 1 != args.len() {
                                    write!(f, ", ")?;
                                }
                            }
                            write!(f, "]")?;
                        }
                    }
                    Ok(())
                }
            }
        }
        go(self, None, env, f)
    }

    pub fn render_to_string(&self, env: &Env) -> InlinableString {
        let mut out = InlinableString::new();
        self.render(&mut out, env).unwrap();
        out
    }
}