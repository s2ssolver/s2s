use std::{
    cmp::min,
    fmt::{Display, Formatter},
    slice::Iter,
};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

use crate::model::{Sort, Variable};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StringTerm {
    Variable(Variable),
    Constant(Vec<char>),
    Concat(Box<StringTerm>, Box<StringTerm>),
}

impl Default for StringTerm {
    fn default() -> Self {
        Self::empty()
    }
}

impl Sorted for StringTerm {
    fn sort(&self) -> Sort {
        Sort::String
    }
}

impl StringTerm {
    /// The empty string
    pub fn empty() -> Self {
        Self::Constant(vec![])
    }

    pub fn is_const(&self) -> Option<Vec<char>> {
        match self {
            StringTerm::Constant(c) => Some(c.to_vec()),
            StringTerm::Variable(_) => None,
            StringTerm::Concat(x, y) => match (x.is_const(), y.is_const()) {
                (Some(x), Some(y)) => Some(x.iter().chain(y.iter()).cloned().collect()),
                _ => None,
            },
        }
    }

    pub fn reverse(&self) -> StringTerm {
        match self {
            StringTerm::Variable(var) => StringTerm::Variable(var.clone()),
            StringTerm::Constant(word) => {
                StringTerm::Constant(word.iter().rev().cloned().collect())
            }
            StringTerm::Concat(lhs, rhs) => StringTerm::concat(rhs.reverse(), lhs.reverse()),
        }
    }

    pub fn constant(str: &str) -> Self {
        Self::Constant(str.chars().collect())
    }

    pub fn variable(var: &Variable) -> Self {
        Self::Variable(var.clone())
    }

    pub fn concat(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (StringTerm::Constant(x), StringTerm::Constant(y)) => {
                StringTerm::Constant(x.iter().chain(y.iter()).cloned().collect())
            }
            (x, y) => StringTerm::Concat(Box::new(x), Box::new(y)),
        }
    }

    pub fn concat_const(lhs: Self, other: &str) -> Self {
        Self::concat(lhs, StringTerm::Constant(other.chars().collect()))
    }

    pub fn concat_var(lhs: Self, var: &Variable) -> Self {
        Self::concat(lhs, StringTerm::Variable(var.clone()))
    }

    pub fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            StringTerm::Variable(var) => {
                if let Some(term) = subs.get(var) {
                    match term {
                        Term::String(s) => s.clone(),
                        _ => panic!("Cannot substitute variable {} with term {}", var, term),
                    }
                } else {
                    self.clone()
                }
            }
            StringTerm::Constant(_) => self.clone(),
            StringTerm::Concat(lhs, rhs) => {
                StringTerm::concat(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
        }
    }
}

impl Alphabet for StringTerm {
    fn alphabet(&self) -> IndexSet<char> {
        match self {
            StringTerm::Variable(_) => IndexSet::new(),
            StringTerm::Constant(word) => word.iter().cloned().collect(),
            StringTerm::Concat(lhs, rhs) => {
                lhs.alphabet().union(&rhs.alphabet()).cloned().collect()
            }
        }
    }
}

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

    pub fn reverse(&self) -> Self {
        Self::new(self.symbols.iter().rev().cloned().collect())
    }

    pub fn ends_with(&self, other: &Self) -> bool {
        self.reverse().starts_with(&other.reverse())
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
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

impl From<StringTerm> for Pattern {
    fn from(value: StringTerm) -> Self {
        match value {
            StringTerm::Variable(var) => Self::variable(&var),
            StringTerm::Constant(word) => Self::constant(&word.iter().collect::<String>()),
            StringTerm::Concat(lhs, rhs) => {
                let mut res = Self::from(*lhs);
                res.extend(Self::from(*rhs));
                res
            }
        }
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

impl Into<StringTerm> for Pattern {
    fn into(self) -> StringTerm {
        let mut res = StringTerm::empty();
        for symbol in self.symbols {
            match symbol {
                Symbol::Constant(c) => res = StringTerm::concat_const(res, &c.to_string()),
                Symbol::Variable(v) => res = StringTerm::concat_var(res, &v),
            }
        }
        res
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

/* Conversions */

impl From<&str> for StringTerm {
    fn from(value: &str) -> Self {
        Self::constant(value)
    }
}

impl From<Variable> for StringTerm {
    fn from(value: Variable) -> Self {
        Self::variable(&value)
    }
}

impl From<(StringTerm, StringTerm)> for WordEquation {
    fn from(value: (StringTerm, StringTerm)) -> Self {
        Self::new(value.0.into(), value.1.into())
    }
}

impl TryFrom<Predicate> for WordEquation {
    type Error = (); // Todo: better error type

    fn try_from(value: Predicate) -> Result<Self, Self::Error> {
        match value {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                Ok(Self::new(lhs.into(), rhs.into()))
            }
            _ => Err(()),
        }
    }
}

impl Into<Predicate> for WordEquation {
    fn into(self) -> Predicate {
        Predicate::Equality(Term::String(self.lhs.into()), Term::String(self.rhs.into()))
    }
}

impl Into<Formula> for WordEquation {
    fn into(self) -> Formula {
        self.into()
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

impl Substitutable for Pattern {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        let mut res = Self::empty();
        for sym in self.symbols() {
            match sym {
                Symbol::Constant(c) => {
                    res.append_word(&c.to_string());
                }
                Symbol::Variable(v) => match sub.get(v) {
                    Some(Term::String(st)) => res.extend(Pattern::from(st.clone())),
                    Some(_) => panic!("Cannot substitute variable {} with non-string term", v),
                    None => todo!(),
                },
            }
        }
        res
    }
}

impl Substitutable for WordEquation {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        Self::new(
            self.lhs.apply_substitution(sub),
            self.rhs.apply_substitution(sub),
        )
    }
}

impl Evaluable for WordEquation {
    fn eval(&self, sub: &Substitution) -> Option<bool> {
        let substituted = self.apply_substitution(sub);
        if substituted.lhs.is_constant() && substituted.rhs.is_constant() {
            Some(substituted.lhs == substituted.rhs)
        } else {
            None
        }
    }
}

impl Display for StringTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StringTerm::Variable(var) => write!(f, "{}", var),
            StringTerm::Constant(word) => write!(f, "{}", word.iter().collect::<String>()),
            StringTerm::Concat(lhs, rhs) => write!(f, "{}{}", lhs, rhs),
        }
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

use super::{
    formula::{Alphabet, Formula, Predicate, Sorted, Term},
    Evaluable, Substitutable, Substitution, VarManager,
};

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

    #[quickcheck]
    fn term_patter_conversion(pat: Pattern) -> bool {
        let t: StringTerm = pat.clone().into();
        pat == t.into()
    }
}
