use num_bigint::BigUint;

use super::{Expression, Symbol};

#[derive(Debug, thiserror::Error)]
pub enum AstError {
    #[error("Unsupported: {0}")]
    Unsupported(String),
    #[error("Undeclared symbol: {0}")]
    Undeclared(Symbol),
    #[error("Only numerals in bounds of isize are supported ({0})")]
    NumeralOutOfBounds(BigUint),
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
    #[error("Syntax error at {position}: {message}")]
    SyntaxError {
        position: smt2parser::Position,
        message: String,
    },
}

impl AstError {
    pub fn neg_existence(e: &Expression) -> Self {
        AstError::Unsupported(format!(
            "Negation of {} introduces universal quantification",
            e
        ))
    }

    pub fn unsupported_expression(e: &Expression) -> Self {
        AstError::Unsupported(e.to_string())
    }

    pub fn unsupported_exprtype(e: impl Into<Expression>) -> Self {
        let e: Expression = e.into();
        AstError::Unsupported(e.to_string())
    }
}
