use std::{collections::HashMap, fmt::Display};

use indexmap::IndexSet;

/// Representation of formulas and predicates
use crate::model::{
    linears::LinearConstraint,
    regex::Regex,
    words::{Pattern, WordEquation},
    Sort, Variable,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    WordEquation(WordEquation),
    RegulaConstraint(Pattern, Regex),
    LinearConstraint(LinearConstraint),
}

impl Predicate {
    /// Create a new predicate from a word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::WordEquation(eq)
    }

    /// Create a new predicate from a regular constraint
    pub fn regular_constraint(p: Pattern, r: Regex) -> Self {
        Self::RegulaConstraint(p, r)
    }

    /// Evaluate the truth value of this atom under the given substitution
    /// Returns None if the substitution is partial and the truth value depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Substitution) -> Option<bool> {
        match self {
            Predicate::WordEquation(eq) => eq.is_solution(substitution),
            Predicate::LinearConstraint(_c) => todo!(),
            Predicate::RegulaConstraint(_p, _r) => todo!(), // Derivate r w.r.t. p.substitute()
        }
    }

    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Predicate::WordEquation(eq) => eq.alphabet(),
            Predicate::LinearConstraint(_) => IndexSet::new(),
            Predicate::RegulaConstraint(_, _) => todo!("Regular Constraints not supported yet"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    Predicate(Predicate),
    BoolVar(Variable),
}

impl Atom {
    /// Create a new atom from a word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::Predicate(Predicate::WordEquation(eq))
    }

    /// Evaluate the truth value of this atom under the given substitution
    /// Returns None if the substitution is partial and the truth value depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Substitution) -> Option<bool> {
        match self {
            Atom::Predicate(p) => p.evaluate(substitution),
            Atom::BoolVar(v) => substitution.get(v).map(|f| match f {
                ConstVal::Bool(b) => b,
                _ => panic!("Variable {} is not a boolean", v),
            }),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Formula {
    /// The constant true
    True,
    /// The constant false
    False,
    /// An atom
    Atom(Atom),
    /// A disjunction
    Or(Vec<Formula>),
    /// A conjunction
    And(Vec<Formula>),
    /// A negation
    Not(Box<Formula>),
}

impl Formula {
    /// Evaluate the formula under the given substitution
    /// Returns None if the substitution is partial and the value of the formula depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Substitution) -> Option<bool> {
        match self {
            Formula::True => Some(true),
            Formula::False => Some(false),
            Formula::Atom(a) => a.evaluate(substitution),
            Formula::Or(fs) => {
                fs.iter()
                    .map(|f| f.evaluate(substitution))
                    .fold(Some(false), |acc, x| match (acc, x) {
                        (Some(true), _) => Some(true),
                        (_, Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        _ => None,
                    })
            }
            Formula::And(fs) => {
                fs.iter()
                    .map(|f| f.evaluate(substitution))
                    .fold(Some(true), |acc, x| match (acc, x) {
                        (Some(false), _) => Some(false),
                        (_, Some(false)) => Some(true),
                        (Some(true), Some(true)) => Some(true),
                        _ => None,
                    })
            }
            Formula::Not(f) => f.evaluate(substitution).map(|x| !x),
        }
    }

    pub fn is_conjunctive(&self) -> bool {
        match self {
            Formula::True | Formula::False | Formula::Atom(_) => true,
            Formula::Or(_) => false,
            Formula::And(fs) => fs.iter().all(Self::is_conjunctive),
            Formula::Not(f) => f.is_conjunctive(),
        }
    }

    pub fn num_atoms(&self) -> usize {
        match self {
            Formula::True | Formula::False | Formula::Atom(_) => 1,
            Formula::Or(fs) | Formula::And(fs) => fs.iter().map(Self::num_atoms).sum(),
            Formula::Not(f) => f.num_atoms(),
        }
    }

    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Formula::True | Formula::False => IndexSet::new(),
            Formula::Atom(a) => match a {
                Atom::Predicate(p) => p.alphabet(),
                Atom::BoolVar(_) => IndexSet::new(),
            },
            Formula::Or(fs) | Formula::And(fs) => fs
                .iter()
                .map(Self::alphabet)
                .fold(IndexSet::new(), |acc, x| acc.union(&x).cloned().collect()),
            Formula::Not(f) => f.alphabet(),
        }
    }
}

/// A constant value
#[derive(Clone, Debug, PartialEq)]
pub enum ConstVal {
    String(Vec<char>),
    Bool(bool),
    Int(isize),
}

impl ConstVal {
    /// Create a new constant value from a string
    pub fn string(s: &str) -> Self {
        Self::String(s.chars().collect())
    }

    /// Create a new constant value from a boolean
    pub fn bool(b: bool) -> Self {
        Self::Bool(b)
    }

    /// Create a new constant value from an integer
    pub fn int(i: isize) -> Self {
        Self::Int(i)
    }

    /// Get the sort of this constant value
    fn sort(&self) -> Sort {
        match self {
            Self::String(_) => Sort::String,
            Self::Bool(_) => Sort::Bool,
            Self::Int(_) => Sort::Int,
        }
    }

    fn default(sort: Sort) -> Self {
        match sort {
            Sort::String => Self::String(Vec::default()),
            Sort::Bool => Self::Bool(bool::default()),
            Sort::Int => Self::Int(isize::default()),
        }
    }
}

/// A substitution of variables
pub struct Substitution {
    assignments: HashMap<Variable, ConstVal>,
    defaults: bool,
}

impl Substitution {
    /// Create a new substitution that maps all variables to their default value
    pub fn with_defaults() -> Self {
        Self {
            assignments: HashMap::new(),
            defaults: true,
        }
    }

    /// Set the value of a variable.
    /// Panics if the variable is already assigned or if the sort of the value does not match the sort of the variable.
    pub fn set(&mut self, var: &Variable, val: ConstVal) {
        if var.sort() != val.sort() {
            panic!(
                "Cannot assign value {} of sort {:?} to variable {} of sort {:?}",
                val,
                val.sort(),
                var,
                var.sort()
            );
        }
        let res = self.assignments.insert(var.clone(), val);
        if res.is_some() {
            panic!("Variable {} already assigned", var);
        }
    }

    /// Set the value of a variable to its default value
    pub fn set_default(&mut self, var: &Variable) {
        self.set(var, ConstVal::default(var.sort()));
    }

    /// Get the value of a variable
    pub fn get(&self, var: &Variable) -> Option<ConstVal> {
        match self.assignments.get(var) {
            Some(x) => Some(x.clone()),
            None => {
                if self.defaults {
                    Some(ConstVal::default(var.sort()))
                } else {
                    None
                }
            }
        }
    }
}

impl From<HashMap<Variable, Vec<char>>> for Substitution {
    fn from(value: HashMap<Variable, Vec<char>>) -> Self {
        let mut sub = Self::with_defaults();
        for (var, val) in value {
            sub.set(&var, ConstVal::String(val));
        }
        sub
    }
}

/* Pretty Printing */

impl Display for ConstVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(s) => write!(f, "\"{}\"", s.iter().collect::<String>()),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Int(i) => write!(f, "{}", i),
        }
    }
}

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::WordEquation(weq) => write!(f, "{}", weq),
            Predicate::RegulaConstraint(_, _) => todo!(),
            Predicate::LinearConstraint(c) => write!(f, "{}", c),
        }
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Predicate(p) => write!(f, "{}", p),
            Atom::BoolVar(v) => write!(f, "{}", v),
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Atom(a) => write!(f, "{}", a),
            Formula::Or(fs) => {
                write!(f, "(")?;
                let mut first = true;
                for fm in fs {
                    if !first {
                        write!(f, r" \/ ")?;
                    }
                    write!(f, "{}", fm)?;
                    first = false;
                }
                write!(f, ")")
            }
            Formula::And(fs) => {
                write!(f, "(")?;
                let mut first = true;
                for fm in fs {
                    if !first {
                        write!(f, r" /\ ")?;
                    }
                    write!(f, "{}", fm)?;
                    first = false;
                }
                write!(f, ")")
            }
            Formula::Not(fm) => write!(f, "¬{}", fm),
        }
    }
}

impl Display for Substitution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (var, val) in self.assignments.iter() {
            write!(f, "{}: {}, ", var, val)?;
        }
        write!(f, "]")
    }
}
