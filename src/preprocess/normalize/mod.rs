mod convert;
mod nf;
mod rewrite;

use convert::convert_expr;
use nf::expression_to_nnf;

use thiserror::Error;

use crate::{
    ast::{ExpressionBuilder, Script, Sort},
    context::Context,
    ir::{Formula, FormulaBuilder},
};

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
pub fn convert(
    script: &Script,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
) -> Result<Formula, NormalizationError> {
    let mut fm_builder = FormulaBuilder::default();

    let mut conjuncts = vec![];
    for expr in script.iter_asserts() {
        let as_nnf = expression_to_nnf(expr, builder)?;
        let fm = convert_expr(&as_nnf, ctx, &mut fm_builder)?;
        conjuncts.push(fm);
    }
    let res = fm_builder.and(conjuncts);
    Ok(res)
}
