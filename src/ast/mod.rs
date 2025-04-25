use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::Index,
    rc::Rc,
};

pub mod error;
mod manager;
pub mod normal;
pub mod smt;
mod subs;
pub mod utils;

use indexmap::IndexSet;
pub use manager::AstBuilder;
use smt_str::{re::Regex, SmtString};
pub use subs::VarSubstitution;

use crate::context::{Sort, Sorted, Variable};

pub type Id = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /* Constants */
    /// Constant Boolean
    Bool(bool),
    /// Constant String
    String(SmtString),
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
    /// Substring
    SubStr,
    /// At
    At,
    /// Replace first occurrence of a substring with another substring
    Replace,
    /// Replace all occurrences of a substring with another substring
    ReplaceAll,

    /// Strint to Int conversion
    ToInt,
    /// Int to String conversion
    FromInt,

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
            NodeKind::Concat
            | NodeKind::Length
            | NodeKind::SubStr
            | NodeKind::At
            | NodeKind::Replace
            | NodeKind::ReplaceAll
            | NodeKind::ToInt
            | NodeKind::FromInt => false,
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => true,
            NodeKind::Add | NodeKind::Neg | NodeKind::Sub | NodeKind::Mul => false,
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => true,
        }
    }

    /// Returns true if the node is a commutative operator.
    /// That is, whether the order of the arguments does not matter.
    pub fn is_commutative(&self) -> bool {
        matches!(
            self,
            NodeKind::Or
                | NodeKind::And
                | NodeKind::Add
                | NodeKind::Mul
                | NodeKind::Eq
                | NodeKind::Equiv
        )
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

    /// Returns a true or false if the formula rooted at this node is trivially true or false.
    /// Otherwise returns None.
    pub fn as_bool_const(&self) -> Option<bool> {
        match self.kind() {
            NodeKind::Bool(b) => Some(*b),
            NodeKind::Or => {
                let mut all_false = true;
                for c in self.children() {
                    match c.as_bool_const() {
                        Some(true) => return Some(true),
                        Some(false) => (),
                        None => all_false = false,
                    }
                }
                if all_false {
                    Some(false)
                } else {
                    None
                }
            }
            NodeKind::And => {
                let mut all_true = true;

                for c in self.children() {
                    match c.as_bool_const() {
                        Some(false) => {
                            return Some(false);
                        }
                        Some(true) => (),
                        None => {
                            all_true = false;
                        }
                    }
                }

                if all_true {
                    Some(true)
                } else {
                    None
                }
            }
            NodeKind::Imp => match self[0].as_bool_const() {
                Some(false) => Some(true),
                Some(true) => self[1].as_bool_const(),
                None => {
                    if self[1].as_bool_const()? {
                        Some(true)
                    } else {
                        None
                    }
                }
            },
            NodeKind::Equiv => Some(self[0].as_bool_const()? == self[1].as_bool_const()?),
            NodeKind::Eq => match (&self[0].sort(), &self[1].sort()) {
                (Sort::String, Sort::String) => {
                    Some(self[0].as_str_const()? == self[1].as_str_const()?)
                }
                (Sort::Int, Sort::Int) => Some(self[0].as_int_const()? == self[1].as_int_const()?),
                _ => None,
            },
            NodeKind::Not => Some(!self[0].as_bool_const()?),
            NodeKind::Ite => {
                if self[0].as_bool_const()? {
                    self[1].as_bool_const()
                } else {
                    self[2].as_bool_const()
                }
            }
            NodeKind::InRe => {
                let lhs = self[0].as_str_const()?;
                if let NodeKind::Regex(re) = &self[1].kind() {
                    Some(re.accepts(&lhs))
                } else {
                    None
                }
            }
            NodeKind::PrefixOf => {
                let pref = self[0].as_str_const()?;
                let of = self[1].as_str_const()?;
                Some(of.starts_with(&pref))
            }
            NodeKind::SuffixOf => {
                let suff = self[0].as_str_const()?;
                let of = self[1].as_str_const()?;
                Some(of.ends_with(&suff))
            }
            NodeKind::Contains => {
                let hay = self[0].as_str_const()?;
                let needle = self[1].as_str_const()?;
                Some(hay.contains(&needle))
            }
            NodeKind::Lt => {
                let l = self[0].as_int_const()?;
                let r = self[1].as_int_const()?;
                Some(l < r)
            }
            NodeKind::Le => {
                let l = self[0].as_int_const()?;
                let r = self[1].as_int_const()?;
                Some(l <= r)
            }
            NodeKind::Gt => {
                let l = self[0].as_int_const()?;
                let r = self[1].as_int_const()?;
                Some(l > r)
            }
            NodeKind::Ge => {
                let l = self[0].as_int_const()?;
                let r = self[1].as_int_const()?;
                Some(l >= r)
            }
            _ => None,
        }
    }

    //TODO: we should use checked operations here
    pub fn as_int_const(&self) -> Option<i64> {
        match self.kind() {
            NodeKind::Int(i) => Some(*i),
            NodeKind::Length => Some(self.as_str_const()?.len() as i64),
            NodeKind::ToInt => {
                let s = self[0].as_str_const()?;
                // convet to positive int base 10, or -1 if not possible
                // todo: double check if the conversion is correct
                match s.to_string().parse::<u32>() {
                    Ok(i) => Some(i as i64),
                    Err(_) => Some(-1),
                }
            }
            NodeKind::Add => {
                let mut sum = 0;
                for c in self.children() {
                    sum += c.as_int_const()?;
                }

                Some(sum)
            }
            NodeKind::Neg => Some(-self[0].as_int_const()?),
            NodeKind::Sub => {
                let mut sum = self[0].as_int_const()?;
                for c in self.children().iter().skip(1) {
                    sum -= c.as_int_const()?;
                }
                Some(sum)
            }
            NodeKind::Mul => {
                let mut prod = 1;
                for c in self.children() {
                    prod *= c.as_int_const()?;
                }
                Some(prod)
            }
            _ => None,
        }
    }

    pub fn as_str_const(&self) -> Option<SmtString> {
        match self.kind() {
            NodeKind::String(s) => Some(s.clone()),
            NodeKind::Concat => {
                let mut res = SmtString::empty();
                for c in self.children() {
                    res.append(&c.as_str_const()?);
                }
                Some(res)
            }
            NodeKind::SubStr => {
                let s = self[0].as_str_const()?;
                let i = self[1].as_int_const()?;
                let l = self[2].as_int_const()?;
                if 0 <= l && 0 <= i {
                    Some(s.drop(i as usize).take(l as usize))
                } else {
                    Some(SmtString::empty())
                }
            }
            NodeKind::At => {
                let s = self[0].as_str_const()?;
                let i = self[1].as_int_const()?;
                if 0 <= i {
                    Some(s.drop(i as usize).take(1))
                } else {
                    Some(SmtString::empty())
                }
            }
            NodeKind::Replace => {
                let s = self[0].as_str_const()?;
                let from = self[1].as_str_const()?;
                let to = self[2].as_str_const()?;
                Some(s.replace(&from, &to))
            }
            NodeKind::ReplaceAll => {
                let s = self[0].as_str_const()?;
                let from = self[1].as_str_const()?;
                let to = self[2].as_str_const()?;
                Some(s.replace_all(&from, &to))
            }
            NodeKind::FromInt => {
                let i = self[0].as_int_const()?;
                if i < 0 {
                    return Some(SmtString::empty());
                } else {
                    Some(i.to_string().into()) // TODO: Double check if this is correct
                }
            }
            _ => None,
        }
    }

    /// Returns the size of the node.
    /// The size of a node is the number of nodes in the tree rooted at this node.
    pub fn size(&self) -> usize {
        1 + self.children.iter().map(|c| c.size()).sum::<usize>()
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

/// Returns the set of all nodes that represent literals in the first order theory
pub fn get_literals(node: &Node) -> IndexSet<Node> {
    let mut lits = IndexSet::new();
    if node.is_literal() {
        lits.insert(node.clone());
    } else {
        for child in node.children() {
            lits.extend(get_literals(child));
        }
    }
    lits
}

/// Returns all nodes that are entailed by this node.
/// This is computed approximately by traversing the tree rooted at this node and collecting all nodes that are children of an And node.
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

/// Returns all literals that are entailed by this node.
/// This is computed approximately by traversing the tree rooted at this node and collecting all nodes that are children of an And node.
/// Note that this works only for nodes that are in canonical form.
pub fn get_entailed_literals(node: &Node) -> IndexSet<Node> {
    let mut lits = IndexSet::new();
    if node.is_literal() {
        lits.insert(node.clone());
    } else if node.kind() == &NodeKind::And {
        for child in node.children() {
            lits.extend(get_entailed_literals(child));
        }
    }
    lits
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
                    unreachable!(
                        "Equality between different sorts ({lhs_sort}, {rhs_sort}): {}",
                        self
                    )
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

            NodeKind::Concat
            | NodeKind::String(_)
            | NodeKind::SubStr
            | NodeKind::At
            | NodeKind::Replace
            | NodeKind::ReplaceAll
            | NodeKind::FromInt => Sort::String,
            NodeKind::InRe | NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => {
                Sort::Bool
            }

            NodeKind::Length
            | NodeKind::Int(_)
            | NodeKind::Add
            | NodeKind::Neg
            | NodeKind::Sub
            | NodeKind::Mul
            | NodeKind::ToInt => Sort::Int,
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
            NodeKind::SubStr => write!(f, "substr"),
            NodeKind::At => write!(f, "at"),
            NodeKind::Replace => write!(f, "replace"),
            NodeKind::ReplaceAll => write!(f, "replaceall"),
            NodeKind::Length => write!(f, "len"),
            NodeKind::InRe => write!(f, "in_re"),
            NodeKind::PrefixOf => write!(f, "prefixof"),
            NodeKind::SuffixOf => write!(f, "suffixof"),
            NodeKind::Contains => write!(f, "contains"),
            NodeKind::ToInt => write!(f, "toint"),
            NodeKind::FromInt => write!(f, "fromint"),
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
            write!(f, "{}", self.kind)
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

    use crate::context::Context;

    use super::*;

    pub fn parse_pattern(s: &str, ctx: &mut Context) -> Node {
        let mut children = Vec::new();
        let mut word = String::new();
        for c in s.chars() {
            if c.is_ascii_lowercase() {
                word.push(c);
            } else if c.is_ascii_uppercase() {
                if !word.is_empty() {
                    children.push(ctx.ast().const_str(&word));
                    word.clear();
                }
                let v = ctx.new_var(c.to_string(), Sort::String).unwrap();
                children.push(ctx.ast().variable(v.clone()));
            } else if c.is_ascii_whitespace() {
                continue;
            } else {
                panic!("Invalid character in pattern: {}", c);
            }
        }
        if !word.is_empty() {
            children.push(ctx.ast().const_str(&word));
        }
        ctx.ast().concat(children)
    }

    pub fn parse_equation(lhs: &str, rhs: &str, ctx: &mut Context) -> Node {
        let lhs = parse_pattern(lhs, ctx);
        let rhs = parse_pattern(rhs, ctx);
        ctx.ast().eq(lhs, rhs)
    }
}
