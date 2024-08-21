mod convert;
mod nf;
mod rewrite;

use convert::convert_expr;
use nf::expression_to_nnf;

use thiserror::Error;

use crate::{
    ast::{Script, Sort},
    context::Context,
    ir::Formula,
};
// TODO: Make struct with type for each error, and a field for the Expression/ExpressionType that caused the error
#[derive(Error, Debug)]
pub enum NormalizationError {
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

/// Converts the script to a formula.
pub fn convert(script: &Script, ctx: &mut Context) -> Result<Formula, NormalizationError> {
    let mut conjuncts = vec![];
    for expr in script.iter_asserts() {
        let as_nnf = expression_to_nnf(expr, ctx.ast_builder())?;
        let fm = convert_expr(&as_nnf, ctx)?;
        conjuncts.push(fm);
    }
    let res = ctx.ir_builder().and(conjuncts);
    Ok(res)
}
