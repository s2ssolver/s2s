use std::{fmt::Display, sync::atomic::AtomicUsize};

use indexmap::{IndexMap, IndexSet};

pub mod linears;
pub mod regex;
pub mod words;

/// The sort of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    String,
    Int,
    Bool,
}

/// Representation of a variable of a certain sort
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    name: String,
    sort: Sort,
}

static VAR_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// A variable. Each variable has a name and a sort.
/// Two variables are equal if they have the same name.
/// Variables should not be created directly, but through a `VarManager`
impl Variable {
    fn new(name: String, sort: Sort) -> Self {
        Variable { name, sort }
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// A manager for variables
#[derive(Debug, Clone, Default)]
pub struct VarManager {
    /// The set of variables, indexed by name
    vars: IndexMap<String, Variable>,
    tmp_vars: IndexSet<Variable>,
}

impl VarManager {
    /// Creates a new variable manager that keeps track of the variables used in the problem
    pub fn new() -> Self {
        Self {
            vars: IndexMap::new(),
            tmp_vars: IndexSet::new(),
        }
    }

    /// Creates and returns a new temporal variable
    /// Temporal variables are not declared in the input problem and are not printed in the output
    pub fn tmp_var(&mut self, sort: Sort) -> Variable {
        let id = VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let name = format!("tmp_{}", id);
        let tvar = Variable::new(name, sort);
        self.tmp_vars.insert(tvar.clone());
        tvar
    }

    /// Creates and returns a new variable.
    /// Panics if a variable with the same name already exists.
    pub fn new_var(&mut self, name: &str, sort: Sort) -> Variable {
        assert!(!self.vars.contains_key(name));
        let v = Variable::new(name.to_owned(), sort);
        self.vars.insert(name.to_owned(), v.clone());
        v
    }

    /// Returns an iterator over the variables of a certain sort.
    /// Includes temporal variables.
    pub fn of_sort(&self, sort: Sort) -> impl Iterator<Item = &Variable> {
        self.vars
            .values()
            .filter(move |v| v.sort == sort)
            .chain(self.tmp_vars.iter().filter(move |v| v.sort == sort))
    }

    /// Returns a variable by name, if it exists
    pub fn by_name(&self, name: &str) -> Option<&Variable> {
        self.vars.get(name)
    }

    /// Returns true if the variable is temporal, false otherwise
    pub fn is_temporal(&self, var: &Variable) -> bool {
        self.tmp_vars.contains(var)
    }
}
