mod nf;
mod rewrite;

use std::rc::Rc;

use thiserror::Error;

use crate::{
    ast::{Expression, ExpressionBuilder, Script, Sort},
    context::Context,
    ir::{Formula, FormulaBuilder},
};

#[derive(Error, Debug)]
pub enum NormalizationError {
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error("invalid sort of {expr}. Expected {expected} but was {got}")]
    InvalidSort {
        expr: Rc<Expression>,
        expected: Sort,
        got: Sort,
    },
    #[error("Negation of {0} introduces unsupported quantifier")]
    InvalidNegationQuantifier(String),
}

pub fn normalize(
    script: &Script,
    builder: &mut ExpressionBuilder,
    ctx: &mut Context,
) -> Result<Formula, NormalizationError> {
    let mut formula_builder = FormulaBuilder::default();
    let rewrite = rewrite::rewrite(script, builder, ctx);
    todo!()
}
