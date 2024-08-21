mod convert;
mod rewrite;
//mod simplify;

use thiserror::Error;

use crate::repr::Sort;

// TODO: Make struct with type for each error, and a field for the Expression/ExpressionType that caused the error
#[derive(Error, Debug)]
pub enum PreprocessingError {
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error("invalid sort of {expr}. Expected {expected} but was {got}")]
    InvalidSort {
        expr: String,
        expected: Sort,
        got: Sort,
    },
    #[error("Negation of {0} introduces unsupported quantifier")]
    InvalidNegationQuantifier(String),
    #[error("Not in NNF: {0}")]
    NotInNNF(String),
}

// 1. Convert
// 2. Simplify
// 3. Rewrite
