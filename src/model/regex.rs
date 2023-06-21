use crate::model::words::Pattern;

use super::words::StringTerm;

/// Represents a terms of sort lang that form regular languages.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReTerm {
    /// An empty language.
    None,
    /// The language containing any character.
    Any,
    /// The language containing all sequences of characters.
    All,
    /// The language containing the given string term.
    String(StringTerm),
    /// The language containing the finite union of the given languages.
    Union(Vec<ReTerm>),
    /// The language containing the concatenation of the given languages.
    Concat(Vec<ReTerm>),
    /// The Kleene closure of a language.
    Star(Box<ReTerm>),
    /// The positive closure of a language.
    Plus(Box<ReTerm>),
    /// The language containing the given language and the empty string.
    Optional(Box<ReTerm>),
    /// The language containing the finite intersection of the given languages.
    Inter(Vec<ReTerm>),
    /// The language containing the difference of the given languages.
    Diff(Box<ReTerm>, Box<ReTerm>),
    /// The language containing the complement of the given language.
    Comp(Box<ReTerm>),
    /// The language containing all words between the given bounds (inclusively).
    /// Is empty if the bounds are not constants of length 1.
    Range(StringTerm, StringTerm),
    /// The language containing all words of the given language raised to the given power.
    Pow(Box<ReTerm>, usize),
    /// The language containing all words of the given language repeated between the given bounds (inclusively).
    Loop(Box<ReTerm>, usize, usize),
}

/// Represents a constraint on a pattern to be contained in a regular language, given by a regular expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RegularConstraint {
    /// The regular expression.
    re: ReTerm,
    /// The variable that is constrained by the regular expression.
    pattern: Pattern,
}

impl ReTerm {
    /// Checks whether the expression is grounded.
    /// Returns true if it does not contain variable symbols and false otherwise.
    pub fn is_grounded(&self) -> bool {
        match self {
            ReTerm::String(p) => p.is_const().is_some(),
            ReTerm::Union(v) | ReTerm::Concat(v) | ReTerm::Inter(v) => {
                v.iter().all(Self::is_grounded)
            }
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _)
            | ReTerm::Loop(r, _, _) => r.is_grounded(),
            ReTerm::Diff(r1, r2) => r1.is_grounded() && r2.is_grounded(),
            ReTerm::Range(p1, p2) => p1.is_const().is_some() && p2.is_const().is_some(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::model::{Sort, Variable};

    use super::*;

    #[test]
    fn test_is_grounded_constant_literal() {
        let r = ReTerm::String(StringTerm::constant("foo"));
        assert!(r.is_grounded());
    }

    #[test]
    fn test_is_grounded_variable_literal() {
        let v = Variable::new(String::from("x"), Sort::String);
        let r = ReTerm::String(StringTerm::variable(&v));
        assert!(!r.is_grounded());
    }
}
