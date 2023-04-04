pub mod regex;
pub mod words;

/// The sort of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    String,
    Int,
}

/// Representation of a variable of a certain sort
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    name: String,
    sort: Sort,
}

impl Variable {
    pub fn new(name: String, sort: Sort) -> Self {
        Variable { name, sort }
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}
