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
}

impl Error {
    pub fn unsupported<T: Into<String>>(msg: T) -> Self {
        Error::Unsupported(msg.into())
    }
}
