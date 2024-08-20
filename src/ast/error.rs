use std::rc::Rc;

use super::{ExprType, Expression};

#[derive(Debug, thiserror::Error)]
pub enum AstError {
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error("Undeclared symbol: {0}")]
    Undeclared(String),
    #[error("Symbol already declared: {0}")]
    AlreadyDeclared(String),
    #[error(transparent)]
    SmtError(#[from] smt2parser::Error),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("Invalid escape sequence: {0}")]
    InvalidEscapeSequence(String),
    #[error("Invalid Unicode code point: {0}")]
    InvalidCodePoint(u32),
}

impl AstError {
    pub fn neg_existence(e: &Rc<Expression>) -> Self {
        AstError::Unsupported(format!(
            "Negation of {} introduces universal quantification",
            e
        ))
    }

    pub fn unsupported_expression(e: &Rc<Expression>) -> Self {
        AstError::Unsupported(e.to_string())
    }

    pub fn unsupported_exprtype(e: impl Into<ExprType>) -> Self {
        let e: ExprType = e.into();
        AstError::Unsupported(e.to_string())
    }
}
