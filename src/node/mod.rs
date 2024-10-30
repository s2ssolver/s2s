use std::{fmt::Display, hash::Hash, ops::Index, rc::Rc};

use crate::context::{Sort, Sorted, Variable};

mod canonical;
pub mod error;
mod manager;
mod normal;
mod subs;
pub mod utils;

pub use manager::NodeManager;
use regulaer::re::Regex;
pub use subs::NodeSubstitution;

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
    InRe,
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
    /// Returns true if the node is an atomic formula.
    /// An atomic formula is a formula if
    /// - it is an equality between two terms
    /// - a predicate/relation in the theory
    /// - a Boolean variable or constant
    pub fn is_atom(&self) -> bool {
        match self {
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => true,
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

    pub fn is_atomic(&self) -> bool {
        self.children.is_empty() && self.kind.is_atom()
    }

    /// Returns true if the node is a literal.
    /// A node is a literal if it is either a an atomic formula or a negation of an atomic formula.
    pub fn is_literal(&self) -> bool {
        if self.kind().is_atom() {
            true
        } else if self.kind() == &NodeKind::Not {
            if let Some(child) = self.children().first() {
                child.kind().is_atom()
            } else {
                unreachable!("Negation node should have a child")
            }
        } else {
            false
        }
    }

    /// Returns true if this node contains the given node as a sub-node.
    pub fn contains(&self, other: &Node) -> bool {
        if self == other.as_ref() {
            return true;
        }
        for child in self.children() {
            if child.contains(other) {
                return true;
            }
        }
        false
    }

    /// Returns an iterator over the children of the node
    pub fn iter(&self) -> impl Iterator<Item = &Node> {
        self.children.iter()
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

impl Index<usize> for OwnedNode {
    type Output = Node;

    /// Returns the child at the given index or panics if the index is out of bounds.
    fn index(&self, index: usize) -> &Self::Output {
        &self.children[index]
    }
}

/* Sorting */

impl Sorted for OwnedNode {
    fn sort(&self) -> Sort {
        match self.kind() {
            NodeKind::Or
            | NodeKind::And
            | NodeKind::Imp
            | NodeKind::Equiv
            | NodeKind::Not
            | NodeKind::Bool(_) => Sort::Bool,

            NodeKind::Eq => {
                debug_assert!(self.children().len() == 2);
                let lhs = self.children().first().unwrap();
                let rhs = self.children().last().unwrap();
                let lhs_sort = lhs.sort();
                let rhs_sort = rhs.sort();
                if lhs_sort == rhs_sort && !rhs_sort.is_bool() {
                    Sort::Bool
                } else {
                    unreachable!("Equality between different sorts ({lhs_sort}, {rhs_sort})",)
                }
            }

            NodeKind::Regex(_) => Sort::RegLan,
            NodeKind::Variable(v) => v.sort(),

            NodeKind::Concat | NodeKind::String(_) => Sort::String,
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => {
                Sort::Bool
            }

            NodeKind::Length | NodeKind::Int(_) | NodeKind::Add | NodeKind::Sub | NodeKind::Mul => {
                Sort::Int
            }
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => Sort::Bool,
        }
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
            NodeKind::InRe => write!(f, "in_re"),
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

#[cfg(test)]
pub mod testutils {
    use crate::{context::Sort, node::Node};

    use super::NodeManager;

    pub fn parse_pattern(s: &str, mngr: &mut NodeManager) -> Node {
        let mut children = Vec::new();
        let mut word = String::new();
        for c in s.chars() {
            if c.is_ascii_lowercase() {
                word.push(c);
            } else if c.is_ascii_uppercase() {
                if !word.is_empty() {
                    children.push(mngr.const_str(&word));
                    word.clear();
                }
                let v = mngr.new_var(c.to_string(), Sort::String).unwrap();
                children.push(mngr.var(v.clone()));
            } else if c.is_ascii_whitespace() {
                continue;
            } else {
                panic!("Invalid character in pattern: {}", c);
            }
        }
        if !word.is_empty() {
            children.push(mngr.const_str(&word));
        }
        mngr.concat(children)
    }

    pub fn parse_equation(lhs: &str, rhs: &str, mngr: &mut NodeManager) -> Node {
        let lhs = parse_pattern(lhs, mngr);
        let rhs = parse_pattern(rhs, mngr);
        mngr.eq(lhs, rhs)
    }
}
