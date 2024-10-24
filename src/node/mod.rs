use std::{fmt::Display, hash::Hash, rc::Rc};

use crate::context::Variable;

mod manager;
mod normal;
mod subs;

pub use manager::NodeManager;
use regulaer::re::Regex;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /* Constants */
    /// Constant Boolean
    Bool(bool),
    /// Constant String
    String(String),
    /// Constant integer
    Int(i64),
    /// Regular expression (using the regulaer crate)
    Regex(Regex),

    /// Variable
    Variable(Rc<Variable>),

    /* Bool Functions */
    /// Disjunction
    Or,
    /// Conjunction
    And,
    /// Implication
    Imp,
    /// Bi-implication
    Equiv,
    /// Negation
    Not,

    /// Equality.
    /// Equalty is overloaded to work with both strings and integers.
    /// Equality between Boolean values is represented as Equiv.
    Eq,

    /* String Functions */
    /// Concatenation
    Concat,
    /// Length
    Length,
    /// Regular Membership
    Memebership,
    /// Prefixof Constraint
    PrefixOf,
    /// Suffixof Constraint
    SuffixOf,
    /// Containment Constraint
    Contains,

    /* Linear Integer Functions */
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Less than
    Lt,
    /// Less than or equal
    Le,
    /// Greater than
    Gt,
    /// Greater than or equal
    Ge,
}

impl NodeKind {
    /// Returns true if the node is a theory predicate.
    /// A theory predicate is a function that returns a boolean value, excluding Boolean functions.
    pub fn is_theory_predicate(&self) -> bool {
        match self {
            NodeKind::Memebership
            | NodeKind::PrefixOf
            | NodeKind::SuffixOf
            | NodeKind::Contains => true,
            _ => false,
        }
    }
}

pub type Node = Rc<OwnedNode>;

#[derive(Debug, Clone)]
pub struct OwnedNode {
    /// Unique identifier
    id: usize,

    /// Type of node
    kind: NodeKind,

    /// List of children
    /// TODO: use smallvec
    children: Vec<Node>,
}

impl OwnedNode {
    pub(super) fn new(id: usize, node_type: NodeKind, children: Vec<Node>) -> Self {
        OwnedNode {
            id,
            kind: node_type,
            children,
        }
    }

    /// Returns [`NodeKind`] of the node
    pub fn kind(&self) -> &NodeKind {
        &self.kind
    }

    /// Returns the children of the node
    pub fn children(&self) -> &[Node] {
        &self.children
    }

    /// Returns true if the node is a constant boolean with value `true`
    pub fn is_true(&self) -> bool {
        matches!(self.kind, NodeKind::Bool(true))
    }

    /// Returns true if the node is a constant boolean with value `false`
    pub fn is_false(&self) -> bool {
        matches!(self.kind, NodeKind::Bool(false))
    }
}

impl Hash for OwnedNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialEq for OwnedNode {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for OwnedNode {}

impl IntoIterator for OwnedNode {
    type Item = Node;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.children.into_iter()
    }
}

/* Pretty */

impl Display for NodeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeKind::Bool(b) => write!(f, "{}", b),
            NodeKind::String(s) => write!(f, "\"{}\"", s),
            NodeKind::Int(i) => write!(f, "{}", i),
            NodeKind::Regex(regex) => write!(f, "{}", regex),
            NodeKind::Variable(v) => write!(f, "{}", v),
            NodeKind::Or => write!(f, "or"),
            NodeKind::And => write!(f, "and"),
            NodeKind::Imp => write!(f, "=>"),
            NodeKind::Equiv => write!(f, "<=>"),
            NodeKind::Not => write!(f, "not"),
            NodeKind::Eq => write!(f, "="),
            NodeKind::Concat => write!(f, "concat"),
            NodeKind::Length => write!(f, "len"),
            NodeKind::Memebership => write!(f, "in_re"),
            NodeKind::PrefixOf => write!(f, "prefixof"),
            NodeKind::SuffixOf => write!(f, "suffixof"),
            NodeKind::Contains => write!(f, "contains"),
            NodeKind::Add => write!(f, "+"),
            NodeKind::Sub => write!(f, "-"),
            NodeKind::Mul => write!(f, "*"),
            NodeKind::Lt => write!(f, "<"),
            NodeKind::Le => write!(f, "<="),
            NodeKind::Gt => write!(f, ">"),
            NodeKind::Ge => write!(f, ">="),
        }
    }
}

impl Display for OwnedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.children().is_empty() {
            return write!(f, "{}", self.kind);
        } else {
            write!(f, "({}", self.kind)?;
            for child in &self.children {
                write!(f, " {}", child)?;
            }
            write!(f, ")")
        }
    }
}
