mod woorpje;

pub use woorpje::WoorpjeEncoder;

use crate::model::words::WordEquation;

use super::PredicateEncoder;

pub trait WordEquationEncoder: PredicateEncoder {
    fn new(equation: WordEquation) -> Self;
}
