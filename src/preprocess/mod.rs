mod convert;
mod normal;
pub mod simp;

use thiserror::Error;

use crate::{
    context::{Context, Sort},
    ir::Formula,
    smt::Symbol,
};

pub use convert::convert_script;

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
    #[error("Undeclared variable: {0}")]
    UndeclaredVariable(Symbol),
    #[error("Variable `{0}` has already been declared")]
    AlreadyDeclared(Symbol),
    #[error("Negation of {0} introduces unsupported quantifier")]
    InvalidNegationQuantifier(String),
    #[error("Not in NNF: {0}")]
    NotInNNF(String),
    #[error("Only linear arithmetic is supporte ({0})")]
    NonLinearArithmetic(String),
}

pub fn normalize(fm: Formula, ctx: &mut Context) -> Result<Formula, PreprocessingError> {
    let mut normalizer = normal::Normalizer::default();
    normalizer.rewrite(fm, ctx)
}
