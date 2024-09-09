use std::{
    cmp::min,
    fmt::{Display, Formatter},
    hash::Hash,
    slice::Iter,
};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

#[cfg(test)]
use crate::context::Context;

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

impl From<char> for Symbol {
    fn from(value: char) -> Self {
        Symbol::Constant(value)
    }
}

impl From<Variable> for Symbol {
    fn from(value: Variable) -> Self {
        Symbol::Variable(value)
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
    pub fn constants(&self) -> IndexSet<char> {
        let mut alphabet = IndexSet::new();
        for symbol in &self.symbols {
            if let Symbol::Constant(c) = symbol {
                alphabet.insert(*c);
            }
        }
        alphabet
    }

    pub fn at(&self, i: usize) -> Option<&Symbol> {
        self.symbols.get(i)
    }

    /// Returns true iff the pattern is a single variable.
    /// This is equivalent to `len() == 1 && symbols[0].is_variable()`.
    pub fn is_variable(&self) -> bool {
        self.symbols.len() == 1 && self.symbols[0].is_variable()
    }

    pub fn as_variable(&self) -> Option<Variable> {
        if self.len() == 1 {
            match self.first().unwrap() {
                Symbol::Constant(_) => None,
                Symbol::Variable(v) => Some(v.clone()),
            }
        } else {
            None
        }
    }

    /// Returns the first symbol of the pattern, if it exists.
    pub fn first(&self) -> Option<&Symbol> {
        self.symbols.first()
    }

    /// Removes the first `n` symbols from the pattern and returns the result.
    /// If `n` is greater than the length of the pattern, the empty pattern is returned.
    pub fn strip_prefix(&self, n: usize) -> Self {
        Self::new(self.symbols[n..].to_vec())
    }

    /// Removes the last `n` symbols from the pattern and returns the result.
    /// If `n` is greater than the length of the pattern, the empty pattern is returned.
    pub fn strip_suffix(&self, n: usize) -> Self {
        Self::new(self.symbols[..self.len() - n].to_vec())
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
    pub fn variables(&self) -> IndexSet<Variable> {
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

    /// Returns the (longest) prefix of the pattern that is constant.
    fn constant_prefix(&self) -> String {
        let mut res = String::new();
        for symbol in &self.symbols {
            match symbol {
                Symbol::Constant(c) => res.push(*c),
                _ => break,
            }
        }
        res
    }

    /// Returns the (longest) suffix of the pattern that is constant.
    fn constant_suffix(&self) -> String {
        let mut res = String::new();
        for symbol in self.symbols.iter().rev() {
            match symbol {
                Symbol::Constant(c) => res.push(*c),
                _ => break,
            }
        }
        res.chars().rev().collect()
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

impl Substitutable for Pattern {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        let mut res = Pattern::empty();
        for s in self.iter() {
            match s {
                Symbol::Constant(_) => res.push(s.clone()),
                Symbol::Variable(v) => {
                    if let Some(subst) = sub.get(v) {
                        let substituee = subst.as_string();
                        res.concat(substituee.clone());
                    } else {
                        res.push(s.clone());
                    }
                }
            }
        }
        res
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

// The actual constraints

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum WordEquation {
    ConstantEquality(String, String),
    VarEquality(Variable, Variable),
    VarAssignment(Variable, String),
    General(Pattern, Pattern),
}

/// Represents a word equation, i.e. an equation between two patterns.
// TODO: Make enum for various types (constant, assignment, variable, general)

impl WordEquation {
    /// Creates a new word equation from two patterns.
    pub fn new(lhs: Pattern, rhs: Pattern) -> Self {
        if lhs.is_constant() && rhs.is_constant() {
            let lhs = lhs.as_constant().unwrap();
            let rhs = rhs.as_constant().unwrap();
            WordEquation::ConstantEquality(lhs, rhs)
        } else if lhs.is_variable() && rhs.is_variable() {
            // Both single variables => Vareq
            let lhs = lhs.as_variable().unwrap();
            let rhs = rhs.as_variable().unwrap();
            WordEquation::VarEquality(lhs, rhs)
        } else if lhs.is_variable() && rhs.is_constant() {
            // Left side variable and right side constants => Assignment
            let lhs = lhs.as_variable().unwrap();
            let rhs = rhs.as_constant().unwrap().chars().collect();
            WordEquation::VarAssignment(lhs, rhs)
        } else if lhs.is_constant() && rhs.is_variable() {
            // Symmetric case
            let lhs = lhs.as_constant().unwrap().chars().collect();
            let rhs = rhs.as_variable().unwrap();
            WordEquation::VarAssignment(rhs, lhs)
        } else {
            // General case
            WordEquation::General(lhs, rhs)
        }
    }

    /// Returns the left-hand side of the word equation.
    pub fn lhs(&self) -> Pattern {
        match self {
            WordEquation::ConstantEquality(lhs, _) => Pattern::constant(lhs),
            WordEquation::VarEquality(lhs, _) | WordEquation::VarAssignment(lhs, _) => {
                Pattern::variable(lhs)
            }
            WordEquation::General(lhs, _) => lhs.clone(),
        }
    }

    /// Returns the right-hand side of the word equation.
    pub fn rhs(&self) -> Pattern {
        match self {
            WordEquation::ConstantEquality(_, rhs) | WordEquation::VarAssignment(_, rhs) => {
                Pattern::constant(rhs)
            }
            WordEquation::VarEquality(_, rhs) => Pattern::variable(rhs),
            WordEquation::General(_, rhs) => rhs.clone(),
        }
    }

    /// Returns the set of variables that occur in the word equation.
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.lhs().variables();
        vars.extend(self.rhs().variables());
        vars
    }

    /// Returns the set of constants that occur in the word equation.
    pub fn constants(&self) -> IndexSet<char> {
        let mut consts = self.lhs().constants();
        consts.extend(self.rhs().constants());
        consts
    }

    /// Reverses both sides of the word equation.
    pub fn reverse(&self) -> Self {
        Self::new(self.lhs().reversed(), self.rhs().reversed())
    }

    /// We call a word equation `proper` if it contains at least one side with both a variable and a constant.
    pub fn is_proper(&self) -> bool {
        (self.lhs().contains_constant() && !self.lhs().is_constant())
            || (self.rhs().contains_constant() && !self.rhs().is_constant())
    }
}
impl TrivialReducible for WordEquation {
    /// If the word equation is trivially true or false:
    /// - if both sides are equal, returns true
    /// - if both sides start with a constant word, returns whether they have a common prefix
    /// - if both sides end with a constant word, returns whether they have a common suffix
    /// - if one side is empty and the other side contains a constant word, returns false
    /// - otherwise, returns None
    fn is_trivial(&self) -> Option<bool> {
        if self.lhs() == self.rhs() {
            return Some(true);
        }

        let lhs_prefix = self.lhs().constant_prefix();
        let rhs_prefix = self.rhs().constant_prefix();
        if !lhs_prefix.starts_with(&rhs_prefix) && !rhs_prefix.starts_with(&lhs_prefix) {
            return Some(false);
        }

        let lhs_suffix = self.lhs().constant_suffix();
        let rhs_suffix = self.rhs().constant_suffix();
        if !lhs_suffix.ends_with(&rhs_suffix) && !rhs_suffix.ends_with(&lhs_suffix) {
            return Some(false);
        }

        if self.lhs().is_empty() && self.rhs().contains_constant() {
            return Some(false);
        }
        if self.rhs().is_empty() && self.lhs().contains_constant() {
            return Some(false);
        }
        None
    }
}

impl Substitutable for WordEquation {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        Self::new(
            self.lhs().apply_substitution(sub),
            self.rhs().apply_substitution(sub),
        )
    }
}
impl Display for WordEquation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            WordEquation::ConstantEquality(l, r) => write!(f, "{} = {}", l, r),
            WordEquation::VarEquality(l, r) => write!(f, "{} = {}", l, r),
            WordEquation::VarAssignment(l, r) => write!(f, "{} = {}", l, r),
            WordEquation::General(l, r) => write!(f, "{} = {}", l, r),
        }
    }
}

/// Parses a word equation from a simple string representation.
/// The patterns (lhs and rhs) must be ascii letters. A lowercase letter is a constant, an uppercase letter is a variable.
/// Creates a new variable for each uppercase letter on-the-fly.
#[cfg(test)]
pub(crate) fn parse_simple_equation(lhs: &str, rhs: &str, ctx: &mut Context) -> WordEquation {
    let lhs = parse_simple_pattern(lhs, ctx);
    let rhs = parse_simple_pattern(rhs, ctx);
    WordEquation::new(lhs, rhs)
}

/// Parses a pattern.
/// The pattern must be ascii letters. A lowercase letter is a constant, an uppercase letter is a variable.
/// Creates a new variable for each uppercase letter on-the-fly.
#[cfg(test)]
pub(crate) fn parse_simple_pattern(pat: &str, ctx: &mut Context) -> Pattern {
    let mut parsed = Pattern::empty();
    for c in pat.chars() {
        let symbol: Symbol = if c.is_ascii_lowercase() {
            c.into()
        } else if c.is_ascii_uppercase() {
            let v = match ctx.get_var(&c.to_string()) {
                Some(v) => v,
                None => ctx.make_var(c.to_string(), Sort::String).unwrap(),
            };
            v.as_ref().clone().into()
        } else {
            panic!("Invalid character in pattern {}: {}", pat, c);
        };
        parsed.push(symbol);
    }
    parsed
}

/// Represents a regular constraint, i.e. a pattern and a regular expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegularConstraint {
    lhs: Pattern,
    re: Regex,
}
impl RegularConstraint {
    /// Creates a new regular constraint from a pattern and a regular expression.
    pub fn new(lhs: Pattern, re: Regex) -> Self {
        Self { lhs, re }
    }

    /// Returns the left-hand side of the regular constraint.
    pub fn pattern(&self) -> &Pattern {
        &self.lhs
    }

    /// Returns the regular expression of the regular constraint.
    pub fn re(&self) -> &Regex {
        &self.re
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        self.pattern().variables()
    }

    pub(crate) fn constants(&self) -> IndexSet<char> {
        let mut alph = self.pattern().constants();
        alph.extend(self.re().operator().alphabet().iter_chars());
        alph
    }
}
impl TrivialReducible for RegularConstraint {
    /// If the constraint is trivial:
    /// - if the pattern is constant (contains no variables), returns whether the pattern is in the language of the regular expression.
    /// - if the regex is empty, returns `Some(false)``
    /// - otherwise, returns `None`
    fn is_trivial(&self) -> Option<bool> {
        if self.re().operator().is_none().unwrap_or(false) {
            return Some(false);
        }
        let pat_c = self.pattern().as_constant()?;
        Some(self.re().accepts(&pat_c.into()))
    }
}
impl Substitutable for RegularConstraint {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        Self::new(self.pattern().apply_substitution(sub), self.re.clone())
    }
}
impl Display for RegularConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ∈ {}", self.lhs, self.re)
    }
}

/// Represents a prefix of constraint, i.e. a pattern that is a prefix of another pattern.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PrefixOf {
    prefix: Pattern,
    of: Pattern,
}
impl PrefixOf {
    /// Creates a new prefix of constraint from two patterns.
    pub fn new(prefix: Pattern, of: Pattern) -> Self {
        Self { prefix, of }
    }

    /// Returns the prefix of the prefix of constraint.
    pub fn prefix(&self) -> &Pattern {
        &self.prefix
    }

    /// Returns the pattern of the prefix of constraint.
    pub fn of(&self) -> &Pattern {
        &self.of
    }

    pub(crate) fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.prefix.variables();
        vars.extend(self.of.variables());
        vars
    }

    pub(crate) fn constants(&self) -> IndexSet<char> {
        let mut consts = self.prefix.constants();
        consts.extend(self.of.constants());
        consts
    }
}
impl Substitutable for PrefixOf {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        Self::new(
            self.prefix.apply_substitution(sub),
            self.of.apply_substitution(sub),
        )
    }
}
impl TrivialReducible for PrefixOf {
    fn is_trivial(&self) -> Option<bool> {
        let prefix_c = self.prefix.as_constant()?;
        let of_c = self.of.as_constant()?;
        Some(of_c.starts_with(&prefix_c))
    }
}
impl Display for PrefixOf {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⊑ {}", self.prefix, self.of)
    }
}

/// Represents a prefix of constraint, i.e. a pattern that is a prefix of another pattern.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SuffixOf {
    suffix: Pattern,
    of: Pattern,
}
impl SuffixOf {
    /// Creates a new suffix of constraint from two patterns.
    pub fn new(suffix: Pattern, of: Pattern) -> Self {
        Self { suffix, of }
    }

    /// Returns the suffix of the suffix of constraint.
    pub fn suffix(&self) -> &Pattern {
        &self.suffix
    }

    /// Returns the pattern of the suffix of constraint.
    pub fn of(&self) -> &Pattern {
        &self.of
    }

    pub(crate) fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.suffix.variables();
        vars.extend(self.of.variables());
        vars
    }

    pub(crate) fn constants(&self) -> IndexSet<char> {
        let mut consts = self.suffix.constants();
        consts.extend(self.of.constants());
        consts
    }
}
impl Substitutable for SuffixOf {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        Self::new(
            self.suffix.apply_substitution(sub),
            self.of.apply_substitution(sub),
        )
    }
}
impl TrivialReducible for SuffixOf {
    fn is_trivial(&self) -> Option<bool> {
        let suffix_c = self.suffix.as_constant()?;
        let of_c = self.of.as_constant()?;
        Some(of_c.ends_with(&suffix_c))
    }
}

impl Display for SuffixOf {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ⊒ {}", self.suffix, self.of)
    }
}

/// Represents a prefix of constraint, i.e. a pattern that is a prefix of another pattern.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Contains {
    needle: Pattern,
    haystack: Pattern,
}
impl Contains {
    /// Creates a new contains constraint from two patterns.
    pub fn new(needle: Pattern, haystack: Pattern) -> Self {
        Self { needle, haystack }
    }

    /// Returns the needle of the contains constraint.
    pub fn needle(&self) -> &Pattern {
        &self.needle
    }

    /// Returns the haystack of the contains constraint.
    pub fn haystack(&self) -> &Pattern {
        &self.haystack
    }

    pub(crate) fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.needle.variables();
        vars.extend(self.haystack.variables());
        vars
    }

    pub(crate) fn constants(&self) -> IndexSet<char> {
        let mut consts = self.needle.constants();
        consts.extend(self.haystack.constants());
        consts
    }
}
impl Substitutable for Contains {
    fn apply_substitution(&self, sub: &super::VarSubstitution) -> Self {
        Self::new(
            self.needle.apply_substitution(sub),
            self.haystack.apply_substitution(sub),
        )
    }
}
impl TrivialReducible for Contains {
    fn is_trivial(&self) -> Option<bool> {
        let needle_c = self.needle.as_constant()?;
        let haystack_c = self.haystack.as_constant()?;
        Some(haystack_c.contains(&needle_c))
    }
}
impl Display for Contains {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} contains {}", self.haystack, self.needle)
    }
}

/* Arbitrary */

use quickcheck;
use regulaer::re::Regex;

use crate::repr::{Sort, Sorted, Variable};

use super::{Substitutable, TrivialReducible};

impl Arbitrary for Symbol {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        fn var_name(g: &mut quickcheck::Gen) -> String {
            let mut name = String::new();
            let alphabet = "abcdefghijklmnopqrstuvwxyz";
            for _ in 0..g.size() {
                name.push(
                    alphabet
                        .chars()
                        .nth(usize::arbitrary(g) % alphabet.len())
                        .unwrap(),
                );
            }
            name
        }

        let choices = &[
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Variable(Variable::new(
                usize::arbitrary(g),
                var_name(g),
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
    use regulaer::re::ReBuilder;

    use crate::context::Context;

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

    #[quickcheck]
    fn strip_length(pat: Pattern, n: usize) -> bool {
        pat.strip_prefix(n).len() == pat.len().saturating_sub(n)
    }

    #[test]
    fn reducible_re_none() {
        let mut ctx = Context::default();
        let re = ctx.ast_builder().re_builder().none();
        let v = ctx.new_temp_var(Sort::String);
        let pat = Pattern::variable(&v);
        let re_constr = RegularConstraint::new(pat, re);
        assert_eq!(re_constr.is_trivial(), Some(true));
    }

    #[quickcheck]
    fn const_prefix_is_const_suffix_reversed(pat: Pattern) -> bool {
        let prefix = pat.constant_prefix();
        let suffix = pat.reversed().constant_suffix();
        suffix == prefix.chars().rev().collect::<String>()
    }

    #[test]
    fn reducible_weq_both_sides_equal_const() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("abc", "abc", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(true));
    }

    #[test]
    fn reducible_weq_both_sides_equal_var() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XY", "XY", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(true));
    }

    #[test]
    fn reducible_weq_both_sides_equal_mixed() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XabY", "XabY", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(true));
    }

    #[test]
    fn reducible_weq_common_prefix_none() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("abcX", "abcY", &mut ctx);
        assert_eq!(eq.is_trivial(), None);
    }

    #[test]
    fn reducible_weq_common_prefix_false() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("abcX", "defY", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(false)); // No common prefix
    }

    #[test]
    fn reducible_weq_common_suffix_none() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("Xabc", "Yabc", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(true)); // Common suffix: "abc"
    }

    #[test]
    fn reducible_weq_common_suffix_false() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("Xabc", "Ydef", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(false)); // No common suffix
    }

    #[test]
    fn reducible_weq_empty_side_with_constant() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("", "abc", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(false)); // One side is empty, the other has a constant

        let eq2 = parse_simple_equation("abc", "", &mut ctx);
        assert_eq!(eq2.is_trivial(), Some(false)); // One side is empty, the other has a constant
    }

    #[test]
    fn reducible_weq_empty_sides() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("", "", &mut ctx);
        assert_eq!(eq.is_trivial(), Some(true)); // Both sides are empty, hence equal
    }
}
