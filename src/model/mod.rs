use std::{collections::HashMap, fmt::Display, sync::atomic::AtomicUsize};

use indexmap::IndexMap;

use self::{
    formula::{Predicate, Term},
    integer::{IntTerm, LinearArithTerm, LinearConstraint, LinearConstraintType},
    regex::Regex,
    words::{StringTerm, WordEquation},
};

pub mod formula;
pub mod integer;
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
    // Whether the variable is transient (i.e. not declared in the input problem)
    transient: bool,
}

static VAR_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// A variable. Each variable has a name and a sort.
/// Two variables are equal if they have the same name.
/// Variables should not be created directly, but through a `VarManager`
impl Variable {
    fn new(name: String, sort: Sort) -> Self {
        Variable {
            name,
            sort,
            transient: false,
        }
    }

    fn new_transient(name: String, sort: Sort) -> Self {
        Variable {
            name,
            sort,
            transient: true,
        }
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn is_int(&self) -> bool {
        self.sort == Sort::Int
    }

    pub fn is_string(&self) -> bool {
        self.sort == Sort::String
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn len_var(&self) -> Self {
        assert!(
            self.sort == Sort::String,
            "Cannot get length of non-string variable {}",
            self
        );
        let name = format!("{}$len", self.name());
        Variable::new_transient(name, Sort::Int)
    }
}

/// A manager for variables
#[derive(Debug, Clone, Default)]
pub struct VarManager {
    /// The set of variables, indexed by name
    vars: IndexMap<String, Variable>,
}

impl VarManager {
    /// Creates a new variable manager that keeps track of the variables used in the problem
    pub fn new() -> Self {
        Self {
            vars: IndexMap::new(),
        }
    }

    /// Creates a new temporal variable and returns a copy of it
    /// Temporal variables are not declared in the input problem and are not printed in the output
    pub fn tmp_var(&mut self, sort: Sort) -> Variable {
        let id = VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let name = format!("tmp_{}", id);
        self.new_var(name.as_str(), sort);
        // set transient flag
        let v = self
            .vars
            .get_mut(&name)
            .expect("Variable should have been created");
        v.transient = true;
        v.clone()
    }

    /// Creates new variable and returns a copy of it.
    /// Panics if a variable with the same name already exists.
    pub fn new_var(&mut self, name: &str, sort: Sort) -> Variable {
        assert!(!self.vars.contains_key(name));
        let v = Variable::new(name.to_owned(), sort);
        self.vars.insert(name.to_owned(), v.clone());
        if sort == Sort::String {
            // also insert a integer variable representing the length of the string
            self.add_var(v.len_var());
        }
        self.by_name(name)
            .expect("Variable should have been created")
            .clone()
    }

    /// Adds an existing variable to the manager.
    /// Prefer using `new_var` or `tmp_var` instead.
    pub fn add_var(&mut self, var: Variable) {
        assert!(!self.vars.contains_key(&var.name));
        if var.sort == Sort::String {
            // also insert a integer variable representing the length of the string
            self.add_var(var.len_var());
        }
        self.vars.insert(var.name.clone(), var);
    }

    /// Returns an iterator over the variables of a certain sort.
    /// If `with_temps` is true, the iterator includes temporal variables.
    pub fn of_sort(&self, sort: Sort, with_temps: bool) -> impl Iterator<Item = &Variable> {
        self.vars
            .values()
            .filter(move |v| v.sort == sort)
            .filter(move |v| if with_temps { true } else { !v.transient })
    }

    /// Returns a variable by name, if it exists
    pub fn by_name(&self, name: &str) -> Option<&Variable> {
        self.vars.get(name)
    }

    /// Returns true if the variable is temporal, false otherwise.
    /// Returns None if the variable does not exist within the scope of the manager.
    pub fn is_temporal(&self, var: &Variable) -> Option<bool> {
        // Don't just check the transient flag, because the variable might not be known by the manager
        self.vars.get(&var.name).map(|v| v.transient)
    }

    /// Returns a variable representing the length of the given variable, if the string variable exists within the manager.
    /// Returns None otherwise.
    /// Panics if the variable is not of sort string
    pub fn str_length_var(&self, var: &Variable) -> Option<&Variable> {
        assert!(
            var.sort == Sort::String,
            "Cannot get length of non-string variable {}",
            var
        );
        let name = format!("{}$len", var.name());

        self.by_name(&name)
    }

    pub fn length_str_var(&self, var: &Variable) -> Option<&Variable> {
        assert!(
            var.sort == Sort::Int,
            "Cannot get length of non-string variable {}",
            var
        );
        let split = var.name().split('$').collect::<Vec<_>>();
        assert_eq!(split.len(), 2);
        assert_eq!(split[1], "len");
        let name = split[0];
        self.by_name(name)
    }

    /// Returns true iff the given variable represents the length of a string variable
    pub fn is_lenght_var(&self, var: &Variable) -> bool {
        self.vars
            .get(&var.name)
            .map(|v| v.name.ends_with("$len"))
            .unwrap_or(false)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
    WordEquation(WordEquation),
    LinearConstraint(LinearConstraint),
    RegularConstraint(Regex),
}

impl From<Predicate> for Constraint {
    fn from(value: Predicate) -> Self {
        match value {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                Constraint::WordEquation(WordEquation::new(lhs.into(), rhs.into()))
            }
            Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Eq));
                Constraint::LinearConstraint(con)
            }
            Predicate::Equality(l, s) => panic!("Cannot create constraint from {} = {}", l, s),
            Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Leq));
                Constraint::LinearConstraint(con)
            }
            Predicate::Leq(lhs, rhs) => panic!("Cannot create constraint from {} <= {}", lhs, rhs),
            Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Less));
                Constraint::LinearConstraint(con)
            }
            Predicate::Less(lhs, rhs) => panic!("Cannot create constraint from {} <= {}", lhs, rhs),
            Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Geq));
                Constraint::LinearConstraint(con)
            }
            Predicate::Geq(lhs, rhs) => panic!("Cannot create constraint from {} <= {}", lhs, rhs),
            Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Greater));
                Constraint::LinearConstraint(con)
            }
            Predicate::Greater(lhs, rhs) => {
                panic!("Cannot create constraint from {} <= {}", lhs, rhs)
            }
            Predicate::In(_, _) => todo!(),
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
                    .insert(var.len_var(), Self::strterm_to_lem(&t).into());
            }
        }
    }

    fn strterm_to_lem(t: &StringTerm) -> IntTerm {
        match t {
            StringTerm::Variable(v) => IntTerm::Var(v.len_var()),
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

    pub fn to_smt2(&self, _var_manager: &VarManager) -> String {
        todo!()
    }
}

impl From<HashMap<Variable, Vec<char>>> for Substitution {
    fn from(value: HashMap<Variable, Vec<char>>) -> Self {
        let mut sub = Self::new();
        for (var, val) in value {
            sub.set(&var, Term::String(words::StringTerm::Constant(val)));
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
        }
    }
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
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
