use thiserror::Error;

use crate::{encode::EncodingError, preprocess::PreprocessingError, smt::AstError};

#[derive(Error, Debug)]
#[error(transparent)]
pub struct PublicError(#[from] pub ErrorRepr);

#[derive(Debug, Error)]
pub enum ErrorRepr {
    /// An error that occured during parsing.
    #[error("failed to construct the AST: {0}")]
    ParseError(AstError),

    /// An error that occured during preprocessing.
    #[error("failed to preprocess: {0}")]
    PreprocessingError(PreprocessingError),

    /// An error that occured during encoding.
    #[error("failed to encode: {0}")]
    EncodingError(EncodingError),
}

// Resolve transitive conversion

impl From<PreprocessingError> for PublicError {
    fn from(err: PreprocessingError) -> Self {
        PublicError(ErrorRepr::PreprocessingError(err))
    }
}

impl From<EncodingError> for PublicError {
    fn from(err: EncodingError) -> Self {
        PublicError(ErrorRepr::EncodingError(err))
    }
}

impl From<AstError> for PublicError {
    fn from(err: AstError) -> Self {
        PublicError(ErrorRepr::ParseError(err))
    }
}
