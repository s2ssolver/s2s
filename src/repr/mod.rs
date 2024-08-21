use std::{fmt::Display, hash::Hash, hash::Hasher};

pub mod ast;
pub mod ir;

pub type Id = usize;

/// The SMT-LIB sorts.
/// Currently, only Int, String, and Bool are supported.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum Sort {
    Int,
    String,
    RegLang,
    Bool,
}
impl Sort {
    /// Returns true if the sort is Bool.
    pub fn is_bool(&self) -> bool {
        matches!(self, Sort::Bool)
    }

    /// Returns true if the sort is Int.
    pub fn is_int(&self) -> bool {
        matches!(self, Sort::Int)
    }

    /// Returns true if the sort is String.
    pub fn is_string(&self) -> bool {
        matches!(self, Sort::String)
    }

    /// Returns true if the sort is RegLang.
    pub fn is_reglang(&self) -> bool {
        matches!(self, Sort::RegLang)
    }
}
impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Int => write!(f, "Int"),
            Sort::String => write!(f, "String"),
            Sort::RegLang => write!(f, "RegLang"),
            Sort::Bool => write!(f, "Bool"),
        }
    }
}
pub trait Sorted {
    fn sort(&self) -> Sort;
}

/// A variable in the SMT-LIB context.
/// Variables are uniquely identified by their name.
/// Every variable has a sort.
#[derive(Debug, Clone)]
pub struct Variable {
    id: Id,
    name: String,
    sort: Sort,
}
impl Variable {
    pub(crate) fn new(id: Id, name: String, sort: Sort) -> Self {
        assert!(!name.chars().any(|c| c == '|'));
        Self { id, name, sort }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the unique identifier of the variable.
    #[allow(dead_code)]
    pub(crate) fn id(&self) -> Id {
        self.id
    }
}
impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Variable {}
impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.name.chars().all(|c| c.is_ascii_alphabetic()) {
            write!(f, "{}", self.name)
        } else {
            write!(f, "|{}|", self.name)
        }
    }
}
impl Sorted for Variable {
    fn sort(&self) -> Sort {
        self.sort
    }
}
