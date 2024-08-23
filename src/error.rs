use thiserror::Error;

use crate::{preprocess::PreprocessingError, repr::ast::AstError};

#[derive(Error, Debug)]
#[error(transparent)]
pub struct PublicError(#[from] pub ErrorRepr);

#[derive(Debug, Error)]
pub enum ErrorRepr {
    /// An error that occured during parsing.
    #[error(transparent)]
    ParseError(AstError),

    /// An error that occured during preprocessing.
    #[error(transparent)]
    PreprocessingError(PreprocessingError),

    /// An error that occured during encoding.
    #[error("failed to encode: {0}")]
    EncodingError(String),

    /// An error that occured during solving.
    #[error("failed solving: {0}")]
    SolverError(String),

    /// An error indicating that the solver does not support the given feature.
    #[error("unsupported: {0}")]
    Unsupported(String),

    /// An otherwise unclassified error.
    #[error("failed: {0}")]
    Other(String),
}

// Resolve transitive conversion

impl From<PreprocessingError> for PublicError {
    fn from(err: PreprocessingError) -> Self {
        PublicError(ErrorRepr::PreprocessingError(err))
    }
}

impl From<AstError> for PublicError {
    fn from(err: AstError) -> Self {
        PublicError(ErrorRepr::ParseError(err))
    }
}
