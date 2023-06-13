//! Representation of quantifier free first-order formulas and predicates

use std::{collections::HashMap, fmt::Display};

use indexmap::IndexSet;

use crate::model::{
    linears::LinearConstraint,
    regex::Regex,
    words::{Pattern, WordEquation},
    Sort, Variable,
};

/// A predicate, which is either a word equation, a regular constraint, or a linear constraint.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    /// A word equation
    WordEquation(WordEquation),
    /// A regular constraint
    RegularConstraint(Pattern, Regex),
    /// A linear constraint
    LinearConstraint(LinearConstraint),
}

impl Predicate {
    /// Create a new predicate from a given word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::WordEquation(eq)
    }

    /// Create a new predicate from a given regular constraint
    pub fn regular_constraint(p: Pattern, r: Regex) -> Self {
        Self::RegularConstraint(p, r)
    }

    /// Evaluate the truth value of this atom under the given substitution
    /// Returns None if the substitution is partial and the truth value depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Assignment) -> Option<bool> {
        match self {
            Predicate::WordEquation(eq) => eq.is_solution(substitution),
            Predicate::LinearConstraint(l) => l.is_solution(substitution),
            Predicate::RegularConstraint(_p, _r) => todo!(), // Derivate r w.r.t. p.substitute()
        }
    }

    /// Returns the alphabet of constants used in this predicate.
    /// For word equations and regular constraints, this is the union of the constant occurring.
    /// For linear constraints, the alphabet is empty.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Predicate::WordEquation(eq) => eq.alphabet(),
            Predicate::LinearConstraint(_) => IndexSet::new(),
            Predicate::RegularConstraint(_, _) => todo!("Regular Constraints not supported yet"),
        }
    }
}

/// An atomic formula.
/// An atomic formula is either a predicate, a boolean variable, or the constant true or false.
#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    /// A predicate
    Predicate(Predicate),
    /// A boolean variable
    BoolVar(Variable),
    /// The constant true
    True,
    /// The constant false
    False,
}

impl Atom {
    /// Create a new atom from a word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::Predicate(Predicate::WordEquation(eq))
    }

    /// Evaluate the truth value of this atom under the given substitution
    /// Returns None if the substitution is partial and the truth value depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Assignment) -> Option<bool> {
        match self {
            Atom::Predicate(p) => p.evaluate(substitution),
            Atom::BoolVar(v) => substitution.get(v).map(|f| match f {
                ConstVal::Bool(b) => b,
                _ => panic!("Variable {} is not a boolean", v),
            }),
            Atom::True => Some(true),
            Atom::False => Some(false),
        }
    }
}

/// A first-order formula with quantifiers.
/// A formula is inductive defined as follows:
/// - An [Atom] is a formula
/// - If `f` is a formula, then `¬f` ([Formula::Not]) is a formula
/// - If `f` and `g` are formulas, then `f ∧ g` ([Formula::And]) and `f ∨ g` ([Formula::Or]) are formulas
///
/// The variants [Formula::Not], [Formula::And], and [Formula::Or] should not be used directly but instead the corresponding constructors [Formula::not], [Formula::and], and [Formula::or], respectively, should be used.
#[derive(Clone, Debug, PartialEq)]
pub enum Formula {
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
    /// Returns the formula `true`
    pub fn ttrue() -> Self {
        Self::Atom(Atom::True)
    }

    /// Returns the formula `false`
    pub fn ffalse() -> Self {
        Self::Atom(Atom::True)
    }

    /// Creates a new formula only consisting of a single Boolean variable
    pub fn bool(var: Variable) -> Self {
        Self::Atom(Atom::BoolVar(var))
    }

    /// Creates a new formula only consisting of a single predicate
    pub fn predicate(pred: Predicate) -> Self {
        Self::Atom(Atom::Predicate(pred))
    }

    /// Creates the conjunction of the given formulas.
    /// Performs some normalization:
    /// - If one of the formulas is `false`, returns `false`
    /// - If one of the formulas is `true`, removes it
    /// - If one of the formulas is a conjunction, adds its conjuncts (i.e. flattens the formula)
    pub fn and(fs: Vec<Formula>) -> Self {
        let mut conjs = Vec::new();
        for f in fs {
            match f {
                Formula::And(fs) => conjs.extend(fs),
                f => conjs.push(f),
            }
        }
        if conjs.is_empty() {
            Self::ttrue()
        } else if conjs.len() == 1 {
            conjs.into_iter().next().unwrap()
        } else {
            Self::And(conjs)
        }
    }

    /// Creates the disjunction of the given formulas.
    /// Performs some normalization:
    /// - If one of the formulas is `true`, returns `true`
    /// - If one of the formulas is `false`, removes it
    /// - If one of the formulas is a disjunction, adds its disjuncts (i.e. flattens the formula)
    pub fn or(fs: Vec<Formula>) -> Self {
        let mut disj = Vec::new();
        for f in fs {
            match f {
                Formula::Or(fs) => disj.extend(fs),
                f => disj.push(f),
            }
        }
        if disj.is_empty() {
            Self::ffalse()
        } else if disj.len() == 1 {
            disj.into_iter().next().unwrap()
        } else {
            Self::Or(disj)
        }
    }

    /// Creates the negation of the given formula.
    /// Flattens double negations.
    pub fn not(f: Formula) -> Self {
        match f {
            Formula::Not(f) => *f,
            f => Self::Not(Box::new(f)),
        }
    }

    /// Evaluate the formula under the given substitution
    /// Returns None if the substitution is partial and the value of the formula depends on the missing assignments.
    pub fn evaluate(&self, substitution: &Assignment) -> Option<bool> {
        match self {
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

    /// Returns `true` if this formula is conjunctive, i.e., if it is a single atom or a conjunction of atoms.
    /// Returns `false` otherwise.
    pub fn is_conjunctive(&self) -> bool {
        match self {
            Formula::Atom(_) => true,
            Formula::Or(_) => false,
            Formula::And(fs) => fs.iter().all(Self::is_conjunctive),
            Formula::Not(f) => f.is_conjunctive(),
        }
    }

    /// Counts the number of atoms in this formula.
    pub fn num_atoms(&self) -> usize {
        match self {
            Formula::Atom(_) => 1,
            Formula::Or(fs) | Formula::And(fs) => fs.iter().map(Self::num_atoms).sum(),
            Formula::Not(f) => f.num_atoms(),
        }
    }

    /// Returns the atoms of this formula that need to be satisfied in every model.
    /// In other words, the conjunction of the returned atoms is entailed by this formula.
    ///
    /// TODO: This should return the asserted literals, not the asserted atoms. That is, it should return a list of atoms and their polarity in which they are asserted.
    pub fn asserted_atoms(&self) -> Vec<&Atom> {
        match self {
            Formula::Atom(a) => vec![a],
            Formula::Or(_fs) => {
                vec![]
            }
            Formula::And(fs) => fs
                .iter()
                .map(Self::asserted_atoms)
                .fold(Vec::new(), |acc, x| acc.into_iter().chain(x).collect()),
            Formula::Not(_f) => vec![],
        }
    }

    /// Returns the alphabet of constants used in this formula.
    /// Collects the alphabet of all predicates occurring in this formula and returns the union of them.
    /// See [Predicate] for more information.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Formula::Atom(a) => match a {
                Atom::Predicate(p) => p.alphabet(),
                Atom::BoolVar(_) => IndexSet::new(),
                Atom::True => IndexSet::new(),
                Atom::False => IndexSet::new(),
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

/// An assignment of constant values to variables
pub struct Assignment {
    assignments: HashMap<Variable, ConstVal>,
    defaults: bool,
}

impl Assignment {
    /// Create a new substitution that maps all variables to their default value
    pub fn with_defaults() -> Self {
        Self {
            assignments: HashMap::new(),
            defaults: true,
        }
    }

    /// Create a new substitution that maps no variables
    pub fn empty() -> Self {
        Self {
            assignments: HashMap::new(),
            defaults: false,
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

impl From<HashMap<Variable, Vec<char>>> for Assignment {
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
            Predicate::RegularConstraint(_, _) => todo!(),
            Predicate::LinearConstraint(c) => write!(f, "{}", c),
        }
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Predicate(p) => write!(f, "{}", p),
            Atom::BoolVar(v) => write!(f, "{}", v),
            Atom::True => write!(f, "true"),
            Atom::False => write!(f, "false"),
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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

impl Display for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (var, val) in self.assignments.iter() {
            write!(f, "{}: {}, ", var, val)?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod test {

    fn formula_and_normalize() {
        todo!()
    }

    fn formula_or_normalize() {
        todo!()
    }

    fn formula_not_normalize() {
        todo!()
    }

    fn formula_conjunctive() {
        todo!()
    }

    fn asserted_atoms_conjunctive() {
        todo!()
    }

    fn asserted_atoms_disjunction() {
        todo!()
    }

    fn asserted_atoms_mixed() {
        todo!()
    }
}
