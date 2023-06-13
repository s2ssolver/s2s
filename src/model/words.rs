use std::{
    cmp::min,
    fmt::{Display, Formatter},
    slice::Iter,
};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

use crate::model::{Sort, Variable};

/// Represents a pattern symbol, which can be either a constant word or a variable.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Symbol {
    /// A constant word
    Constant(char),
    /// A variable. If the sort is not string, then the program will panic at runtime
    Variable(Variable),
}

impl Symbol {
    fn is_string_sort(&self) -> bool {
        match self {
            Symbol::Constant(_) => true,
            Symbol::Variable(v) => v.sort() == Sort::String,
        }
    }

    /// Returns true iff the symbol is a constant word.
    pub fn is_constant(&self) -> bool {
        matches!(self, Symbol::Constant(_))
    }

    /// Returns true iff the symbol is a variable.
    pub fn is_variable(&self) -> bool {
        matches!(self, Symbol::Variable(_))
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

    fn new(symbols: Vec<Symbol>) -> Self {
        Self { symbols }
    }

    pub fn constant(word: &str) -> Self {
        let mut symbols = vec![];
        for c in word.chars() {
            symbols.push(Symbol::Constant(c));
        }
        Self::new(symbols)
    }

    pub fn variable(var: &Variable) -> Self {
        Self::new(vec![Symbol::Variable(var.clone())])
    }

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

    /// Returns the first symbol of the pattern, if it exists.
    pub fn first(&self) -> Option<&Symbol> {
        self.symbols.first()
    }

    /// Returns the last symbol of the pattern, if it exists.
    pub fn last(&self) -> Option<&Symbol> {
        self.symbols.last()
    }

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
    pub fn append(&mut self, symbol: &Symbol) {
        if !symbol.is_string_sort() {
            panic!("Variables in patterns must be of sort String")
        }
        self.symbols.push(symbol.clone())
    }

    pub fn append_var(&mut self, var: &Variable) -> &mut Self {
        self.append(&Symbol::Variable(var.clone()));
        self
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

    pub fn append_word(&mut self, word: &str) -> &mut Self {
        for c in word.chars() {
            self.append(&Symbol::Constant(c));
        }
        self
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
            .any(|x| matches!(x, Symbol::Constant(_)))
    }

    pub fn symbols(&self) -> Iter<Symbol> {
        self.symbols.iter()
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

    pub fn reverse(&self) -> Self {
        Self::new(self.symbols.iter().rev().cloned().collect())
    }

    pub fn ends_with(&self, other: &Self) -> bool {
        self.reverse().starts_with(&other.reverse())
    }

    /// Returns true iff the pattern is empty.
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

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct WordEquation {
    lhs: Pattern,
    rhs: Pattern,
}

impl WordEquation {
    pub fn new(lhs: Pattern, rhs: Pattern) -> Self {
        Self { lhs, rhs }
    }

    /// Returns the empty word equation.
    pub fn empty() -> Self {
        Self::new(Pattern::empty(), Pattern::empty())
    }

    /// Parses a word equation from two strings, where lowercase chars are interpreted as constants and uppercase chars are interpreted as variables.
    pub fn parse_simple(lhs: &str, rhs: &str) -> Self {
        let mut pat_lhs = Pattern::empty();
        for c in lhs.chars() {
            if c.is_lowercase() {
                pat_lhs.append_word(&c.to_string());
            } else {
                pat_lhs.append_var(&Variable::new(c.to_string(), Sort::String));
            }
        }
        let mut pat_rhs = Pattern::empty();
        for c in rhs.chars() {
            if c.is_lowercase() {
                pat_rhs.append_word(&c.to_string());
            } else {
                pat_rhs.append_var(&Variable::new(c.to_string(), Sort::String));
            }
        }
        Self::new(pat_lhs, pat_rhs)
    }

    /// Creates a new equation from two constant strings.
    pub fn constant(lhs: &str, rhs: &str) -> Self {
        Self::new(Pattern::constant(lhs), Pattern::constant(rhs))
    }

    pub fn lhs(&self) -> &Pattern {
        &self.lhs
    }

    pub fn rhs(&self) -> &Pattern {
        &self.rhs
    }

    /// Reverses both sides of the equation.
    pub fn reverse(&self) -> Self {
        Self::new(self.rhs.reverse(), self.lhs.reverse())
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        self.lhs.vars().union(&self.rhs.vars()).cloned().collect()
    }

    /// Returns the set of symbols that occur in the equation.
    pub fn symbols(&self) -> IndexSet<Symbol> {
        let mut res = IndexSet::new();
        res.extend(self.lhs.symbols().cloned());
        res.extend(self.rhs.symbols().cloned());
        res
    }

    pub fn alphabet(&self) -> IndexSet<char> {
        self.lhs
            .alphabet()
            .union(&self.rhs.alphabet())
            .cloned()
            .collect()
    }
}

/* Substitution */

impl Substitutable for Pattern {
    fn substitute(&self, subs: &super::VarSubstitutions) -> Self {
        let mut res = Pattern::empty();
        for symbol in &self.symbols {
            match symbol {
                Symbol::Constant(_) => res.append(symbol),
                Symbol::Variable(var) => match subs.get_str(var) {
                    Some(p) => res.extend(p.clone()),
                    _ => res.append(symbol),
                },
            }
        }
        res
    }
}

impl Substitutable for WordEquation {
    fn substitute(&self, subs: &super::VarSubstitutions) -> Self {
        Self::new(self.lhs.substitute(subs), self.rhs.substitute(subs))
    }
}

impl Proposition for WordEquation {
    fn truth_value(&self) -> Option<bool> {
        if self.lhs.is_constant() && self.rhs.is_constant() {
            Some(self.lhs == self.rhs)
        } else {
            None
        }
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

impl Display for WordEquation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
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

// Arbitrary generation of patterns

use quickcheck;

use super::{Proposition, Substitutable, VarManager};

impl Arbitrary for Symbol {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let mut var_manager = VarManager::new();
        let choices = &[
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Variable(var_manager.tmp_var(Sort::String)),
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

impl Arbitrary for WordEquation {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        WordEquation::new(Pattern::arbitrary(g), Pattern::arbitrary(g))
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
            "x".to_string(),
            Sort::String,
        ))]);
        assert!(!pattern.is_constant());
    }

    #[test]
    fn is_constant_with_mixed_pattern() {
        let mut pat = Pattern::empty();
        pat.append_word("foo")
            .append_var(&Variable::new("x".to_string(), Sort::String))
            .append_word("bar");
        assert!(!pat.is_constant());
    }

    #[quickcheck]
    fn pattern_reverse_reverse_is_identity(pat: Pattern) -> bool {
        pat == pat.reverse().reverse()
    }

    #[quickcheck]
    fn equation_reverse_reverse_is_identity(eq: WordEquation) -> bool {
        eq == eq.reverse().reverse()
    }
}
