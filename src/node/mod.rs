use std::{
    cell::RefCell,
    fmt::{Debug, Display},
    hash::Hash,
    ops::Index,
    rc::Rc,
};

use crate::context::{Sort, Sorted, Variable};

pub mod canonical;
pub mod error;
mod manager;
pub mod normal;
mod subs;
pub mod utils;

use canonical::Literal;
use indexmap::IndexSet;
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

    /// If-then-else
    Ite,

    /// Equality.
    /// Equalty is overloaded to work with both strings and integers.
    /// Equality between Boolean values is represented as Equiv.
    /// It is a logical error to construct Eq nodes with children of of different sorts or of sort Bool.
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
    /// Negation of an integer
    Neg,
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
            NodeKind::String(_) | NodeKind::Int(_) | NodeKind::Regex(_) => false,
            NodeKind::Variable(b) => b.sort().is_bool(),
            NodeKind::Bool(_) => true,
            NodeKind::Or
            | NodeKind::And
            | NodeKind::Imp
            | NodeKind::Equiv
            | NodeKind::Not
            | NodeKind::Ite => false,
            NodeKind::Eq => true,
            NodeKind::Concat | NodeKind::Length => false,
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => true,
            NodeKind::Add | NodeKind::Neg | NodeKind::Sub | NodeKind::Mul => false,
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => true,
        }
    }

    /// If this node is a variable, returns a reference to the variable.
    /// Otherwise, returns None.
    pub fn as_variable(&self) -> Option<&Rc<Variable>> {
        match self {
            NodeKind::Variable(v) => Some(v),
            _ => None,
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

    canonical: RefCell<Option<Literal>>,
}

impl OwnedNode {
    pub(super) fn new(id: usize, node_type: NodeKind, children: Vec<Node>) -> Self {
        OwnedNode {
            id,
            kind: node_type,
            children,
            canonical: RefCell::new(None),
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

    /// Returns true if the node is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self.kind, NodeKind::Variable(_))
    }

    /// Returns true if the node is a constant.
    /// A node is a constant if it is a boolean, string, integer, or regex constant.
    pub fn is_const(&self) -> bool {
        matches!(
            self.kind,
            NodeKind::Bool(_) | NodeKind::String(_) | NodeKind::Int(_) | NodeKind::Regex(_)
        )
    }

    /// Returns true if the node is an atomic proposition within the theory.
    pub fn is_atomic(&self) -> bool {
        self.kind.is_atom()
    }

    /// Returns true if the node is a literal in the theory.
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

    /// Returns true if the node is a pure boolean function, i.e., its arguments are all boolean and it returns a boolean.
    /// Boolean variables and constants are not considered boolean functions.
    /// In other words, this returns true iff the kind of the node is one of the following:
    /// - Or
    /// - And
    /// - Imp
    /// - Equiv
    /// - Not
    pub fn is_bool_fun(&self) -> bool {
        matches!(
            self.kind,
            NodeKind::Or | NodeKind::And | NodeKind::Imp | NodeKind::Equiv | NodeKind::Not
        )
    }

    pub fn variables(&self) -> IndexSet<Rc<Variable>> {
        let mut vars = IndexSet::new();
        for child in self.children() {
            vars.extend(child.variables());
        }
        if let NodeKind::Variable(v) = self.kind() {
            vars.insert(v.clone());
        }
        vars
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

    pub fn as_variable(&self) -> Option<&Rc<Variable>> {
        if let NodeKind::Variable(v) = self.kind() {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_int_const(&self) -> Option<i64> {
        if let NodeKind::Int(i) = self.kind() {
            Some(*i)
        } else {
            None
        }
    }

    /// Attaches data to the node and returns the old data if it exists.
    pub(super) fn set_canonical(&self, canonical: Literal) -> Option<Literal> {
        let mut borrow = self.canonical.borrow_mut();
        let old = borrow.replace(canonical);
        old
    }

    pub fn canonical(&self) -> Option<Literal> {
        self.canonical.borrow().clone()
    }

    /// Detaches the data from the node and returns it.
    /// Returns None if no data is attached.
    pub fn detach(&self) -> Option<Literal> {
        let mut borrow = self.canonical.borrow_mut();
        borrow.take()
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

pub fn get_entailed(node: &Node) -> IndexSet<Node> {
    let mut entailed = IndexSet::new();
    entailed.insert(node.clone());
    if node.kind() == &NodeKind::And {
        for child in node.children() {
            entailed.extend(get_entailed(child));
        }
    }
    entailed
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

            NodeKind::Ite => {
                debug_assert!(self.children().len() == 3);
                let cond = self.children().first().unwrap();
                let then = self.children().get(1).unwrap();
                let els = self.children().last().unwrap();
                if cond.sort().is_bool() {
                    let then_sort = then.sort();
                    let els_sort = els.sort();
                    if then_sort == els_sort {
                        then_sort
                    } else {
                        unreachable!("If-then-else with different sorts ({then_sort}, {els_sort})")
                    }
                } else {
                    unreachable!("Condition of if-then-else is not a boolean")
                }
            }

            NodeKind::Regex(_) => Sort::RegLan,
            NodeKind::Variable(v) => v.sort(),

            NodeKind::Concat | NodeKind::String(_) => Sort::String,
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => {
                Sort::Bool
            }

            NodeKind::Length
            | NodeKind::Int(_)
            | NodeKind::Add
            | NodeKind::Neg
            | NodeKind::Sub
            | NodeKind::Mul => Sort::Int,
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
            NodeKind::Ite => write!(f, "ite"),
            NodeKind::Eq => write!(f, "="),
            NodeKind::Concat => write!(f, "concat"),
            NodeKind::Length => write!(f, "len"),
            NodeKind::InRe => write!(f, "in_re"),
            NodeKind::PrefixOf => write!(f, "prefixof"),
            NodeKind::SuffixOf => write!(f, "suffixof"),
            NodeKind::Contains => write!(f, "contains"),
            NodeKind::Add => write!(f, "+"),
            NodeKind::Sub | NodeKind::Neg => write!(f, "-"),
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
