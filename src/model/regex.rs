use crate::model::words::Pattern;

/// Represents a regular expression, which can match strings of characters.
///
/// This enum can be used to construct and manipulate regular expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum Regex {
    /// An empty regular expression that matches the empty string.
    None,
    /// A regular expression that matches any single character.
    Any,
    /// A regular expression that matches any sequence of characters.
    All,
    /// A regular expression that matches a specific pattern of characters.
    Literal(Pattern),
    /// A regular expression that matches any of several alternative regular expressions.
    Union(Vec<Regex>),
    /// A regular expression that matches the concatenation of several other regular expressions.
    Concat(Vec<Regex>),
    /// A regular expression that matches zero or more occurrences of a regular expression.
    Star(Box<Regex>),
    /// A regular expression that matches one or more occurrences of a regular expression.
    Plus(Box<Regex>),
    /// A regular expression that optionally matches a regular expression.
    Optional(Box<Regex>),
    /// A regular expression that matches the intersection of two or more regular expressions.
    Inter(Vec<Regex>),
    /// A regular expression that matches the difference of two regular expressions.
    Diff(Box<Regex>, Box<Regex>),
    /// A regular expression that matches any character that is not matched by another regular expression.
    Comp(Box<Regex>),
    /// A regular expression that matches any character in the given range.
    Range(Pattern, Pattern),
    /// A regular expression that matches a regular expression raised to a power (number of repetitions).
    Pow(Box<Regex>, usize),
    /// A regular expression that matches a regular expression repeated a certain number of times within a range.
    Loop(Box<Regex>, usize, usize),
}

impl Regex {
    /// Checks whether the expression is grounded.
    /// Returns true if it does not contain variable symbols and false otherwise.
    pub fn is_grounded(&self) -> bool {
        match self {
            Regex::Literal(p) => p.is_constant(),
            Regex::Union(v) | Regex::Concat(v) | Regex::Inter(v) => v.iter().all(Self::is_grounded),
            Regex::Star(r)
            | Regex::Plus(r)
            | Regex::Optional(r)
            | Regex::Comp(r)
            | Regex::Pow(r, _)
            | Regex::Loop(r, _, _) => r.is_grounded(),
            Regex::Diff(r1, r2) => r1.is_grounded() && r2.is_grounded(),
            Regex::Range(p1, p2) => p1.is_constant() && p2.is_constant(),
            _ => false,
        }
    }
}

mod tests {
    use super::*;
    use crate::model::words::Symbol;
    use crate::model::{Sort, Variable};

    #[test]
    fn test_is_grounded_constant_literal() {
        let p = Pattern::from(vec![
            Symbol::LiteralWord(String::from("foo")),
            Symbol::LiteralWord(String::from("bar")),
        ]);
        let r = Regex::Literal(p);
        assert!(r.is_grounded());
    }

    #[test]
    fn test_is_grounded_variable_literal() {
        let p = Pattern::from(vec![
            Symbol::LiteralWord(String::from("foo")),
            Symbol::Variable(Variable::new("X".to_owned(), Sort::String)),
        ]);
        let r = Regex::Literal(p);
        assert!(!r.is_grounded());
    }
}
