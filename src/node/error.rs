use super::Sort;

use super::Node;

/// The error type that can occur when working with nodes
#[derive(Debug, thiserror::Error)]
pub enum NodeError {
    #[error("Variable {0} of sort {1} already declared with sort {2}")]
    AlreadyDeclared(String, Sort, Sort),

    #[error("The node {0} is not in negation normal form")]
    NotInNegationNormalForm(Node),

    #[error("The node {0} is not well-formed")]
    NotWellFormed(Node),

    #[error("Expected sort {1} but got {2} (in {0})")]
    SortMismatch(Node, Sort, Sort),

    #[error("Non-linear integer arithmetic is not supported ({0})")]
    NonLinearArithmetic(Node),
}
