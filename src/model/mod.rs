use std::{collections::HashMap, fmt::Display, sync::atomic::AtomicUsize};

use indexmap::IndexMap;

use crate::{
    instance::Instance,
    sat::{pvar, PVar},
};

use self::terms::{IntTerm, StringTerm, Term};

pub mod constraints;
pub mod formula;

pub mod regex;
pub mod terms;

// Re-exports
pub use constraints::Constraint;

/// The sort of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    String,
    Int,
    Bool,
    ReLang,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Variable {
    String { name: String },
    Int { name: String },
    Bool { name: String, value: PVar },
}

static VAR_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// A variable. Each variable has a name and a sort.
/// Two variables are equal if they have the same name.
/// Variables should not be created directly, but through a `Instance`
impl Variable {
    /// Creates a new variable with the given name and sort.
    pub fn new(name: String, sort: Sort) -> Self {
        match sort {
            Sort::String => Variable::String { name },
            Sort::Int => Variable::Int { name },
            Sort::Bool => Variable::Bool {
                name,
                value: pvar(),
            },
            Sort::ReLang => todo!(),
        }
    }

    /// Creates a new temporal variable of the given sort.
    ///
    /// # Example
    /// ```
    /// use satstr::model::{Variable, Sort};
    /// let str_var = Variable::temp(Sort::String);
    /// let bool_var = Variable::temp(Sort::Bool);
    /// assert!(str_var.is_string());
    /// assert!(bool_var.is_bool());
    /// ```
    pub fn temp(sort: Sort) -> Self {
        let id = VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let name = format!("tmp_{}", id);
        Self::new(name, sort)
    }

    /// Returns the sort of the variable
    /// # Example
    /// ```
    /// use satstr::model::{Variable, Sort};
    /// assert_eq!(Variable::temp(Sort::Bool).sort(), Sort::Bool);
    /// ```
    pub fn sort(&self) -> Sort {
        match self {
            Variable::String { .. } => Sort::String,
            Variable::Int { .. } => Sort::Int,
            Variable::Bool { .. } => Sort::Bool,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Variable::Int { .. })
    }

    pub fn is_string(&self) -> bool {
        matches!(self, Variable::String { .. })
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, Variable::Bool { .. })
    }

    pub fn name(&self) -> &str {
        match self {
            Variable::String { name } => name,
            Variable::Int { name } => name,
            Variable::Bool { name, .. } => name,
        }
    }

    /// Returns a variable representing the length of the this variable, if the variable is of sort string.
    /// Returns None otherwise.
    pub fn len_var(&self) -> Option<Self> {
        let name = format!("{}$len", self.name());
        match self {
            Variable::String { .. } => Some(Variable::Int { name }),
            Variable::Int { .. } => None,
            Variable::Bool { .. } => None,
        }
    }

    /// Returns true if the variable represents the length of a string variable.
    pub fn is_len_var(&self) -> bool {
        self.name().ends_with("$len")
    }

    pub fn len_str_var(&self) -> Option<Variable> {
        let mut split = self.name().split("$");
        let name = split.next()?;
        if split.next() == Some("len") {
            Some(Variable::String {
                name: name.to_string(),
            })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Substitution {
    subs: IndexMap<Variable, Term>,
    use_defaults: bool,
}

/// A substitution of [variables](Variable) by terms.
/// A variable of sort [string](Sort::String) can be substituted by [Pattern], a variable of sort [int](Sort::Int) can be substituted by an [IntArithTerm].
impl Substitution {
    pub fn new() -> Self {
        Self {
            subs: IndexMap::new(),
            use_defaults: false,
        }
    }

    pub fn use_defaults(&mut self) {
        self.use_defaults = true;
    }

    pub fn is_empty(&self) -> bool {
        self.subs.is_empty()
    }

    /// Returns true if the substitution is an assignemt.
    /// We call a substitution an assignment if it substitutes variables with constants.
    pub fn is_assignment(&self) -> bool {
        for (_, val) in &self.subs {
            if !val.is_const() {
                return false;
            }
        }
        true
    }

    pub fn get(&self, var: &Variable) -> Option<&Term> {
        self.subs.get(var)
    }

    pub fn set(&mut self, var: &Variable, term: Term) {
        self.subs.insert(var.clone(), term.clone());
        if var.is_string() {
            if let Term::String(t) = term {
                self.subs
                    .insert(var.len_var().unwrap(), Self::strterm_to_lem(&t).into());
            }
        }
    }

    fn strterm_to_lem(t: &StringTerm) -> IntTerm {
        match t {
            StringTerm::Variable(v) => IntTerm::Var(v.len_var().unwrap()),
            StringTerm::Constant(w) => IntTerm::Const(w.len() as isize),
            StringTerm::Concat(l, r) => {
                IntTerm::plus(&Self::strterm_to_lem(l), &Self::strterm_to_lem(r))
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Term)> {
        self.subs.iter()
    }

    /// Calculates the composition of two substitutions.
    /// The result is the substitution that results from applying the given substitution to this substitution.
    /// If the given substitution defines variables that are not defined in this substitution, the result will contain these variables.
    pub fn compose(&self, other: &Self) -> Self {
        let mut sub = Self::new();
        for (var, val) in &self.subs {
            let chained = val.apply_substitution(other);
            sub.set(var, chained);
        }
        for (var, val) in &other.subs {
            // Add the substitution if it is not yet present
            if sub.get(var).is_none() {
                sub.set(var, val.clone());
            }
        }
        sub
    }

    /// Returns the SMT-LIB representation of the substitution.
    pub fn to_smt2(&self, _instance: &Instance) -> String {
        todo!()
    }
}

impl From<HashMap<Variable, Vec<char>>> for Substitution {
    fn from(value: HashMap<Variable, Vec<char>>) -> Self {
        let mut sub = Self::new();
        for (var, val) in value {
            sub.set(&var, Term::String(StringTerm::Constant(val)));
        }
        sub
    }
}

pub trait Substitutable {
    // TODO: Return Result<Self, Error>
    fn apply_substitution(&self, sub: &Substitution) -> Self;
}

pub trait Evaluable: Substitutable {
    // TODO: Return Result<Self, Error>
    fn eval(&self, sub: &Substitution) -> Option<bool>;
}

/* Pretty Printing */

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::String => write!(f, "String"),
            Sort::Int => write!(f, "Int"),
            Sort::Bool => write!(f, "Bool"),
            Sort::ReLang => write!(f, "ReLang"),
        }
    }
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Variable::String { name } => write!(f, "{}", name),
            Variable::Int { name } => write!(f, "{}", name),
            Variable::Bool { name, value } => write!(f, "{}[{}]", name, value),
        }
    }
}

impl Display for Substitution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (var, val) in &self.subs {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{} -> {}", var, val)?;
        }

        Ok(())
    }
}
