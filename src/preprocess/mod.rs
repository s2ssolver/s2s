mod convert;
mod normal;
//mod simplify;

use thiserror::Error;

use crate::{
    context::Context,
    repr::{ir::Formula, Sort},
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
    #[error("Negation of {0} introduces unsupported quantifier")]
    InvalidNegationQuantifier(String),
    #[error("Not in NNF: {0}")]
    NotInNNF(String),
}

pub fn normalize(fm: &Formula, ctx: &mut Context) -> Result<Formula, PreprocessingError> {
    let mut normalizer = normal::Normalizer::default();
    normalizer.rewrite(fm.clone(), ctx)
}
