use std::{collections::HashSet, hash::Hash, slice::Iter};

use crate::model::{Sort, Variable};

/// Represents a pattern symbol, which can be either a constant word or a variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Symbol {
    /// A constant word
    LiteralWord(String),
    /// A variable. If the sort is not string, then the program will panic at runtime
    Variable(Variable),
}

impl Symbol {
    fn is_string_sort(&self) -> bool {
        match self {
            Symbol::LiteralWord(_) => true,
            Symbol::Variable(v) => v.sort() == Sort::String,
        }
    }
}

/// A pattern is a sequence of symbols, which can be either constant words or variables (of sort String).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    symbols: Vec<Symbol>,
}

impl Pattern {
    /// Creates a new empty pattern.
    pub fn empty() -> Self {
        Self { symbols: vec![] }
    }

    fn new(symbols: Vec<Symbol>) -> Self {
        Self { symbols: symbols }
    }

    /// Returns the alphabet of the pattern, i.e. the set of constant characters that occur in the pattern.
    pub fn alphabet(&self) -> HashSet<char> {
        let mut alphabet = HashSet::new();
        for symbol in &self.symbols {
            if let Symbol::LiteralWord(word) = symbol {
                for c in word.chars() {
                    if !alphabet.contains(&c) {
                        alphabet.insert(c);
                    }
                }
            }
        }
        alphabet
    }

    /// Returns the set of variables that occur in the pattern.
    pub fn vars(&self) -> HashSet<Variable> {
        self.symbols
            .iter()
            .filter_map(|x| match x {
                Symbol::Variable(v) => Some(v),
                _ => None,
            })
            .cloned()
            .collect()
    }

    /// Appends a symbol to the end of the pattern.
    ///
    /// # Panics
    ///
    /// Panics if the given symbol is not of sort String.
    pub fn append(&mut self, symbol: &Symbol) {
        if !symbol.is_string_sort() {
            panic!("Variables in patterns must be of sort String")
        }
        self.symbols.push(symbol.clone())
    }

    /// Prepends a symbol to the beginning of the pattern.
    ///
    /// # Panics
    ///
    /// Panics if the given symbol is not of sort String.
    pub fn prepend(&mut self, symbol: &Symbol) {
        if !symbol.is_string_sort() {
            panic!("Variables in patterns must be of sort String")
        }
        self.symbols.insert(0, symbol.clone())
    }

    /// Returns true iff the pattern does not contain any variables
    pub fn is_constant(&self) -> bool {
        !self
            .symbols
            .iter()
            .any(|x| matches!(x, Symbol::Variable(_)))
    }

    /// Returns true iff the pattern contains at least one constant word
    pub fn contains_constant(&self) -> bool {
        self.symbols
            .iter()
            .any(|x| matches!(x, Symbol::LiteralWord(_)))
    }

    pub fn symbols(&self) -> Iter<Symbol> {
        self.symbols.iter()
    }
}

impl From<Vec<Symbol>> for Pattern {
    fn from(value: Vec<Symbol>) -> Self {
        Self::new(value)
    }
}

impl IntoIterator for Pattern {
    type Item = Symbol;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.symbols.into_iter()
    }
}

/// Normalizes a pattern by concatenating consecutive `LiteralWord` symbols into a single `LiteralWord`.
///
/// # Examples
///
/// ```
/// use crate::normalize_pattern;
///
/// let pattern = vec![
///     Symbol::LiteralWord("hello".to_owned()),
///     Symbol::LiteralWord("world".to_owned()),
/// ];
/// assert_eq!(
///     normalize_pattern(&pattern),
///     vec![Symbol::LiteralWord("helloworld".to_owned())],
/// );
/// ```
///
/// # Arguments
///
/// * `pattern`: A reference to a vector of `Symbol` values representing the pattern to normalize.
///
/// # Returns
///
/// A vector of `Symbol` values representing the normalized pattern.
///
/// # Panics
///
/// This function will panic at runtime if a `Variable` symbol has a sort other than `Sort::String`.
///
/// # Notes
///
/// This function modifies the input pattern by consuming the `Symbol` values. If you need to preserve the input pattern,
/// you should make a copy of it before calling this function.
fn normalize_pattern(pattern: Pattern) -> Pattern {
    let mut res = vec![];
    let mut last_literal: Option<String> = None;
    for symbol in pattern.into_iter() {
        match symbol {
            Symbol::LiteralWord(w) => {
                last_literal
                    .get_or_insert_with(|| String::new())
                    .push_str(&w);
            }
            Symbol::Variable(v) => {
                if v.sort() != Sort::String {
                    panic!("Patterns must only contain variables of sort String");
                }
                last_literal
                    .take()
                    .filter(|x| !x.is_empty())
                    .map(Symbol::LiteralWord)
                    .map(|x| res.push(x));
                res.push(Symbol::Variable(v.clone()));
            }
        }
    }
    last_literal
        .filter(|x| !x.is_empty())
        .map(Symbol::LiteralWord)
        .map(|x| res.push(x));
    Pattern::new(res)
}

pub struct WordEquation {
    lhs: Pattern,
    rhs: Pattern,
}

impl WordEquation {
    pub fn new(lhs: Pattern, rhs: Pattern) -> Self {
        Self {
            lhs: normalize_pattern(lhs),
            rhs: normalize_pattern(rhs),
        }
    }

    pub fn lhs(&self) -> &Pattern {
        &self.lhs
    }

    pub fn rhs(&self) -> &Pattern {
        &self.rhs
    }

    pub fn variables(&self) -> HashSet<Variable> {
        self.lhs.vars().union(&self.rhs.vars()).cloned().collect()
    }

    pub fn alphabet(&self) -> HashSet<char> {
        self.lhs
            .alphabet()
            .union(&self.rhs.alphabet())
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize_pattern_empty() {
        let pattern = Pattern::empty();
        assert_eq!(normalize_pattern(pattern), Pattern::empty());
    }

    #[test]
    fn normalize_pattern_single_literal() {
        let pattern = Pattern::new(vec![Symbol::LiteralWord("foo".to_owned())]);
        assert_eq!(
            normalize_pattern(pattern).symbols,
            vec![Symbol::LiteralWord("foo".to_owned())]
        );
    }

    #[test]
    fn normalize_pattern_multiple_literals() {
        let pattern = Pattern::new(vec![
            Symbol::LiteralWord("foo".to_owned()),
            Symbol::LiteralWord("bar".to_owned()),
            Symbol::LiteralWord("baz".to_owned()),
        ]);
        assert_eq!(
            normalize_pattern(pattern).symbols,
            vec![Symbol::LiteralWord("foobarbaz".to_owned())]
        );
    }

    #[test]
    fn normalize_pattern_single_variable() {
        let pattern = Pattern::new(vec![Symbol::Variable(Variable::new(
            "X".to_owned(),
            Sort::String,
        ))]);
        assert_eq!(
            normalize_pattern(pattern).symbols,
            vec![Symbol::Variable(Variable::new(
                "X".to_owned(),
                Sort::String
            )),]
        );
    }

    #[test]
    fn normalize_empty_strings() {
        let pattern = Pattern::new(vec![
            Symbol::LiteralWord("".to_owned()),
            Symbol::LiteralWord("".to_owned()),
        ]);
        assert_eq!(normalize_pattern(pattern).symbols, vec![]);
    }

    #[test]
    fn normalize_remove_empty_string() {
        let pattern = Pattern::new(vec![
            Symbol::LiteralWord("".to_owned()),
            Symbol::Variable(Variable::new("X".to_owned(), Sort::String)),
        ]);
        assert_eq!(
            normalize_pattern(pattern).symbols,
            vec![Symbol::Variable(Variable::new(
                "X".to_owned(),
                Sort::String
            )),]
        );
    }

    #[test]
    fn normalize_pattern_literals_and_variables() {
        let pattern = Pattern::new(vec![
            Symbol::LiteralWord("foo".to_owned()),
            Symbol::Variable(Variable::new("X".to_owned(), Sort::String)),
            Symbol::LiteralWord("bar".to_owned()),
            Symbol::LiteralWord("baz".to_owned()),
        ]);
        assert_eq!(
            normalize_pattern(pattern).symbols,
            vec![
                Symbol::LiteralWord("foo".to_owned()),
                Symbol::Variable(Variable::new("X".to_owned(), Sort::String)),
                Symbol::LiteralWord("barbaz".to_owned()),
            ]
        );
    }

    #[test]
    fn is_constant_with_empty_pattern() {
        let pattern = Pattern::new(vec![]);
        assert!(pattern.is_constant());
    }

    #[test]
    fn is_constant_with_constant_pattern() {
        let pattern = Pattern::new(vec![Symbol::LiteralWord("foo".to_string())]);
        assert!(pattern.is_constant());
    }

    #[test]
    fn is_constant_with_variable_pattern() {
        let pattern = Pattern::new(vec![Symbol::Variable(Variable::new(
            "x".to_string(),
            Sort::String,
        ))]);
        assert!(!pattern.is_constant());
    }

    #[test]
    fn is_constant_with_mixed_pattern() {
        let pattern = Pattern::new(vec![
            Symbol::LiteralWord("foo".to_string()),
            Symbol::Variable(Variable::new("x".to_string(), Sort::String)),
            Symbol::LiteralWord("bar".to_string()),
        ]);
        assert!(!pattern.is_constant());
    }
}
