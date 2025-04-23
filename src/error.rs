use thiserror::Error;

use crate::{ast::error::NodeError, encode::EncodingError, smt::AstError};

#[derive(Error, Debug)]
#[error(transparent)]
pub struct PublicError(#[from] pub ErrorRepr);

#[derive(Debug, Error)]
pub enum ErrorRepr {
    /// An error that occured during parsing.
    #[error("failed to construct the AST: {0}")]
    Parsing(AstError),

    /// An error that occured during encoding.
    #[error("failed to encode: {0}")]
    Encoding(EncodingError),

    #[error("node error: {0}")]
    Node(NodeError),
}

// Resolve transitive conversion

impl From<EncodingError> for PublicError {
    fn from(err: EncodingError) -> Self {
        PublicError(ErrorRepr::Encoding(err))
    }
}

impl From<AstError> for PublicError {
    fn from(err: AstError) -> Self {
        PublicError(ErrorRepr::Parsing(err))
    }
}

impl From<NodeError> for PublicError {
    fn from(err: NodeError) -> Self {
        PublicError(ErrorRepr::Node(err))
    }
}
