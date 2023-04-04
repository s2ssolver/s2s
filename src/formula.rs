/// Representation of formulas and predicates
use crate::model::{
    regex::Regex,
    words::{Pattern, WordEquation},
};

enum Predicate {
    WordEquation(WordEquation),
    RegulaConstraint(Pattern, Regex),
}

enum Atom {
    Predicate(Predicate),
    BoolVar(usize),
}

pub enum Formula {
    Atom(Atom),
    Or(Vec<Formula>),
    And(Vec<Formula>),
    Not(Box<Formula>),
}
