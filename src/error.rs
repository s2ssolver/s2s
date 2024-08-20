use thiserror::Error;

use crate::ast::AstError;

#[derive(Error, Debug)]
#[error(transparent)]
pub struct PublicError(#[from] pub ErrorRepr);

#[derive(Debug, Error)]
pub enum ErrorRepr {
    /// An error that occured during parsing.
    #[error(transparent)]
    ParseError(AstError),

    /// An error that occured during encoding.
    #[error("Failed to encode: {0}")]
    EncodingError(String),

    /// An error that occured during solving.
    #[error("Failed solving: {0}")]
    SolverError(String),

    /// An error indicating that the solver does not support the given feature.
    #[error("Unsupported: {0}")]
    Unsupported(String),

    /// An otherwise unclassified error.
    #[error("Failed: {0}")]
    Other(String),
}
