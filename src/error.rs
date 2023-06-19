use crate::parse::ParseError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Error {
    /// An error that occured during parsing.
    ParseError(ParseError),

    /// An error that occured during encoding.
    EncodingError(String),

    /// An error that occured during solving.
    SolverError(String),
}
