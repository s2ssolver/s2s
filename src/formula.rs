/// Representation of formulas and predicates
use crate::model::{
    regex::Regex,
    words::{Pattern, WordEquation},
};

#[derive(Clone, Debug, PartialEq)]
pub enum Predicate {
    WordEquation(WordEquation),
    RegulaConstraint(Pattern, Regex),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    Predicate(Predicate),
    BoolVar(usize),
}

impl Atom {
    /// Create a new atom from a word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::Predicate(Predicate::WordEquation(eq))
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
