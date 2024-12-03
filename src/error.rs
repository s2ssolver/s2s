use thiserror::Error;

use crate::{encode::EncodingError, node::error::NodeError, smt::AstError};

#[derive(Error, Debug)]
#[error(transparent)]
pub struct PublicError(#[from] pub ErrorRepr);

#[derive(Debug, Error)]
pub enum ErrorRepr {
    /// An error that occured during parsing.
    #[error("failed to construct the AST: {0}")]
    ParseError(AstError),

    /// An error that occured during encoding.
    #[error("failed to encode: {0}")]
    EncodingError(EncodingError),

    #[error("node error: {0}")]
    NodeError(NodeError),
}

// Resolve transitive conversion

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

impl From<NodeError> for PublicError {
    fn from(err: NodeError) -> Self {
        PublicError(ErrorRepr::NodeError(err))
    }
}
