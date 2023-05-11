use std::{fmt::Display, sync::atomic::AtomicUsize};

pub mod regex;
pub mod words;

/// The sort of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    String,
    Int,
    Bool,
}

/// Representation of a variable of a certain sort
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    name: String,
    sort: Sort,
}

static VAR_COUNTER: AtomicUsize = AtomicUsize::new(1);

impl Variable {
    pub fn new(name: String, sort: Sort) -> Self {
        Variable { name, sort }
    }

    pub fn tmp_var(sort: Sort) -> Self {
        let id = VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let name = format!("tmp_{}", id);
        Self::new(name, sort)
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
