use std::fmt::Display;

use crate::parse::ParseError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Error {
    /// An error that occured during parsing.
    ParseError(ParseError),

    /// An error that occured during encoding.
    EncodingError(String),

    /// An error that occured during solving.
    SolverError(String),

    /// An error indicating that the solver does not support the given feature.
    Unsupported(String),

    /// An otherwise unclassified error.
    Other(String),
}

impl Error {
    pub fn unsupported<T: Into<String>>(msg: T) -> Self {
        Error::Unsupported(msg.into())
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Error::ParseError(e) => write!(f, "Parse error: {}", e),
            Error::EncodingError(e) => write!(f, "Encoding error: {}", e),
            Error::SolverError(e) => write!(f, "Solver error: {}", e),
            Error::Unsupported(e) => write!(f, "Unsupported: {}", e),
            Error::Other(e) => write!(f, "Error: {}", e),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            ParseError::SyntaxError(msg) => write!(f, "Syntax error: {}", msg),

            ParseError::Other(msg) => write!(f, "Error: {}", msg),

            ParseError::Unsupported(msg) => write!(f, "Unsupported: {}", msg),
            ParseError::UnknownIdentifier(msg) => write!(f, "Unknown identifier: {}", msg),
            ParseError::FileNotFound(msg) => write!(f, "File not found: {}", msg),
        }
    }
}
