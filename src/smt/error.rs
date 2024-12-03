use num_bigint::BigUint;

use super::Symbol;

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
