use inlinable_string::InlinableString;
use std::collections::HashMap;
use std::sync::Arc;
use anyhow::Result;

use crate::value::Value;

#[derive(Debug, Clone)]
pub enum RuleResult {
    Exp(Value),
    Intrinsic(usize)
}

#[derive(Debug, Clone)]
pub struct Rule {
    pub condition: Value,
    pub result: RuleResult,
}

#[derive(Clone, Debug)]
pub struct Operation {
    pub commutative: bool,
    pub associative: bool,
}

pub type Bindings = HashMap<InlinableString, Value>;
pub type Ops = HashMap<InlinableString, Operation>;
pub type Ruleset = HashMap<InlinableString, Vec<Rule>>;
pub type Intrinsics = dyn Fn(usize, &Bindings) -> Result<Value> + Sync + Send;

#[derive(Clone)]
pub struct Env {
    pub ops: Arc<Ops>,
    pub ruleset: Vec<Arc<Ruleset>>,
    pub intrinsics: Arc<Intrinsics>,
    pub bindings: Bindings
}

impl Env {
    // Get details about an operation, falling back to the default of not commutative/associative if none exists
    pub fn get_op(&self, name: &InlinableString) -> Operation {
        self.ops.get(name).map(Clone::clone).unwrap_or(Operation { commutative: false, associative: false })
    }

    // Make a new Env with this extra ruleset in it
    pub fn with_ruleset(&self, ruleset: Arc<Ruleset>) -> Self {
        let mut new_env = self.clone();
        new_env.ruleset.push(ruleset);
        new_env
    }

    pub fn with_bindings(&self, bindings: &Bindings) -> Self {
        let mut new_env = self.clone();
        new_env.bindings = bindings.clone();
        new_env
    }
}