mod woorpje;

use std::collections::HashSet;

pub use woorpje::WoorpjeEncoder;

use crate::model::{
    words::{Symbol, WordEquation},
    Variable,
};

use super::{PredicateEncoder, VariableBounds};

pub trait WordEquationEncoder: PredicateEncoder {
    fn new(equation: WordEquation) -> Self;
}
