use std::{
    cmp::min,
    fmt::{Display, Formatter},
    hash::Hash,
    slice::Iter,
};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

/// Represents a pattern symbol, which can be either a constant word or a variable.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Symbol {
    /// A constant word
    Constant(char),
    /// A variable
    Variable(Variable),
}

impl Symbol {
    /// Returns true iff the symbol is a constant word.
    /// This is equivalent to `!is_variable()`.
    pub fn is_constant(&self) -> bool {
        matches!(self, Symbol::Constant(_))
    }

    /// Returns true iff the symbol is a constant word.
    /// This is equivalent to `!is_constant()`.
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::Symbol;
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert!(Symbol::Variable(Variable::temp(Sort::String)).is_variable());
    /// assert!(!Symbol::Constant('a').is_variable());
    /// ```
    pub fn is_variable(&self) -> bool {
        matches!(self, Symbol::Variable(_))
    }

    /// Returns true iff the symbol is of sort String.
    fn valid(&self) -> bool {
        match self {
            Symbol::Constant(_) => true,
            Symbol::Variable(v) => v.sort() == Sort::String,
        }
    }
}

/// A pattern is a sequence of symbols, which can be either constant words or variables (of sort String).
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Pattern {
    symbols: Vec<Symbol>,
}

impl Pattern {
    /// Creates a new empty pattern.
    pub fn empty() -> Self {
        Self { symbols: vec![] }
    }

    /// Creates a new pattern from a sequence of symbols.
    pub fn new(symbols: Vec<Symbol>) -> Self {
        Self { symbols }
    }

    /// Creates a new pattern from a constant word, given as a string.
    pub fn constant(word: &str) -> Self {
        let mut symbols = vec![];
        for c in word.chars() {
            symbols.push(Symbol::Constant(c));
        }
        Self::new(symbols)
    }

    /// Creates a new pattern from a variable.
    pub fn variable(var: &Variable) -> Self {
        Self::new(vec![Symbol::Variable(var.clone())])
    }

    /// Returns the length of the pattern.
    /// This is the number of symbols in the pattern.
    /// Variables are counted as one symbol.
    /// Constants are counted as their length in unicode characters.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns the alphabet of the pattern, i.e. the set of constant characters that occur in the pattern.
    pub fn alphabet(&self) -> IndexSet<char> {
        let mut alphabet = IndexSet::new();
        for symbol in &self.symbols {
            if let Symbol::Constant(c) = symbol {
                alphabet.insert(*c);
            }
        }
        alphabet
    }

    /// Returns true iff the pattern is a single variable.
    /// This is equivalent to `len() == 1 && symbols[0].is_variable()`.
    pub fn is_variable(&self) -> bool {
        self.symbols.len() == 1 && self.symbols[0].is_variable()
    }

    /// Returns the first symbol of the pattern, if it exists.
    pub fn first(&self) -> Option<&Symbol> {
        self.symbols.first()
    }

    /// Returns the last symbol of the pattern, if it exists.
    pub fn last(&self) -> Option<&Symbol> {
        self.symbols.last()
    }

    /// Counts the number of occurrences of the given symbol in the pattern.
    pub fn count(&self, symbol: &Symbol) -> usize {
        self.symbols.iter().filter(|x| x == &symbol).count()
    }

    /// Returns the set of variables that occur in the pattern.
    pub fn vars(&self) -> IndexSet<Variable> {
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
    pub fn push(&mut self, symbol: Symbol) {
        debug_assert!(
            symbol.valid(),
            "Variables in patterns must be of sort String"
        );
        self.symbols.push(symbol)
    }

    pub fn push_var(&mut self, var: Variable) -> &mut Self {
        debug_assert!(
            var.sort() == Sort::String,
            "Variables in patterns must be of sort String"
        );
        self.push(Symbol::Variable(var.clone()));
        self
    }

    pub fn push_word(&mut self, word: &str) -> &mut Self {
        for c in word.chars() {
            self.push(Symbol::Constant(c));
        }
        self
    }

    pub fn concat(&mut self, other: Self) {
        self.symbols.extend(other.symbols)
    }

    /// Replaces all occurrences of the given symbol in the pattern with the given replacement and returns the result.
    pub fn replace(&self, symbol: &Symbol, replacement: &Pattern) -> Self {
        let mut res = vec![];
        for s in &self.symbols {
            if s == symbol {
                res.extend(replacement.symbols.iter().cloned());
            } else {
                res.push(s.clone());
            }
        }
        Self::new(res)
    }

    /// Prepends a symbol to the beginning of the pattern.
    ///
    /// # Panics
    ///
    /// Panics if the given symbol is not of sort String.
    pub fn prepend(&mut self, symbol: &Symbol) {
        debug_assert!(
            symbol.valid(),
            "Variables in patterns must be of sort String"
        );
        self.symbols.insert(0, symbol.clone())
    }

    /// Returns true iff the pattern does not contain any variables
    pub fn is_constant(&self) -> bool {
        !self
            .symbols
            .iter()
            .any(|x| matches!(x, Symbol::Variable(_)))
    }

    /// Returns the pattern as a constant word, if it is a constant word.
    /// Returns `None` if the pattern contains any variables.
    pub fn as_constant(&self) -> Option<String> {
        let mut res = String::new();
        for symbol in &self.symbols {
            match symbol {
                Symbol::Constant(c) => res.push(*c),
                _ => return None,
            }
        }
        Some(res)
    }

    /// Returns true iff the pattern contains at least one constant word
    pub fn contains_constant(&self) -> bool {
        self.symbols
            .iter()
            .any(|x| matches!(x, Symbol::Constant(_)))
    }

    pub fn symbols(&self) -> Iter<Symbol> {
        self.symbols.iter()
    }

    pub fn iter(&self) -> Iter<Symbol> {
        self.symbols()
    }

    /// Returns the factor of the pattern between the given indices.
    /// If indices are out of bounds, they are clamped to the pattern length.
    /// Returns `None` if `i > j`.
    pub fn factor(&self, i: usize, j: usize) -> Option<Self> {
        if i > j {
            return None;
        }
        let i = min(i, self.symbols.len());
        let j = min(j, self.symbols.len());
        Some(Self::new(self.symbols[i..j].to_vec()))
    }

    pub fn extend(&mut self, other: Self) {
        self.symbols.extend(other.symbols.into_iter())
    }

    pub fn starts_with(&self, other: &Self) -> bool {
        if other.len() > self.len() {
            return false;
        }
        for (i, symbol) in other.symbols.iter().enumerate() {
            if symbol != &self.symbols[i] {
                return false;
            }
        }
        true
    }

    /// Reverses the pattern.
    pub fn reversed(&self) -> Self {
        Self::new(self.symbols.iter().rev().cloned().collect())
    }

    pub fn ends_with(&self, other: &Self) -> bool {
        self.reversed().starts_with(&other.reversed())
    }

    /// Returns true iff the pattern contains the given pattern as a factor.
    pub fn contains(&self, other: &Self) -> bool {
        if other.len() > self.len() {
            return false;
        }
        for i in 0..=(self.len() - other.len()) {
            if self.factor(i, i + other.len()).unwrap() == *other {
                return true;
            }
        }
        false
    }

    /// Returns true iff the pattern is empty.
    /// This is equivalent to `len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl std::ops::Index<usize> for Pattern {
    type Output = Symbol;

    fn index(&self, index: usize) -> &Self::Output {
        &self.symbols[index]
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

/* Pretty Printing */
impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for symbol in &self.symbols {
            match symbol {
                Symbol::Constant(word) => write!(f, "{}", word)?,
                Symbol::Variable(var) => write!(f, "{}", var)?,
            }
        }
        Ok(())
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Constant(c) => write!(f, "{}", c),
            Symbol::Variable(v) => write!(f, "{}", v),
        }
    }
}

/* Arbitrary */

use quickcheck;

use crate::repr::{Sort, Sorted, Variable};

impl Arbitrary for Symbol {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choices = &[
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Variable(Variable::new(
                usize::arbitrary(g),
                String::arbitrary(g),
                Sort::String,
            )),
        ];

        g.choose(choices).unwrap().clone()
    }
}

impl Arbitrary for Pattern {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let mut symbols = vec![];
        for _ in 0..g.size() {
            symbols.push(Symbol::arbitrary(g));
        }
        Self::new(symbols)
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn is_constant_with_empty_pattern() {
        let pattern = Pattern::new(vec![]);
        assert!(pattern.is_constant());
    }

    #[test]
    fn is_constant_with_constant_pattern() {
        let pattern = Pattern::constant("foo");
        assert!(pattern.is_constant());
    }

    #[test]
    fn is_constant_with_variable_pattern() {
        let pattern = Pattern::new(vec![Symbol::Variable(Variable::new(
            0,
            "x".to_string(),
            Sort::String,
        ))]);
        assert!(!pattern.is_constant());
    }

    #[test]
    fn is_constant_with_mixed_pattern() {
        let mut pat = Pattern::empty();
        pat.push_word("foo")
            .push_var(Variable::new(0, "x".to_string(), Sort::String))
            .push_word("bar");
        assert!(!pat.is_constant());
    }

    #[quickcheck]
    fn pattern_empty_len_zero_equiv(pat: Pattern) {
        assert_eq!(pat.is_empty(), pat.is_empty());
    }

    #[quickcheck]
    fn pattern_reverse_reverse_is_identity(pat: Pattern) -> bool {
        pat == pat.reversed().reversed()
    }
}
