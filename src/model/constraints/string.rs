use std::{
    cmp::min,
    fmt::{Display, Formatter},
    slice::Iter,
};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

use crate::model::{
    terms::{ReTerm, Term},
    Evaluable, Sort, Substitutable, Substitution, Variable,
};

/// Represents a pattern symbol, which can be either a constant word or a variable.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Symbol {
    /// A constant word
    Constant(char),
    /// A variable
    Variable(Variable),
}

impl Symbol {
    /// Returns true iff the symbol is of sort String.
    fn is_string_sort(&self) -> bool {
        match self {
            Symbol::Constant(_) => true,
            Symbol::Variable(v) => v.sort() == Sort::String,
        }
    }

    /// Returns true iff the symbol is a constant word.
    /// This is equivalent to `!is_variable()`.
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::Symbol;
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert!(Symbol::Constant('a').is_constant());
    /// assert!(!Symbol::Variable(Variable::temp(Sort::String)).is_constant());
    /// ```
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
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::Pattern;
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert_eq!(Pattern::constant("foo").len(), 3);
    /// assert_eq!(Pattern::constant("𝄞").len(), 1);
    /// assert_eq!(Pattern::empty().len(), 0);
    /// assert_eq!(Pattern::variable(&Variable::temp(Sort::String)).len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns the alphabet of the pattern, i.e. the set of constant characters that occur in the pattern.
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::Pattern;
    /// use satstr::model::{Variable, Sort};
    /// use indexmap::indexset;
    /// assert_eq!(Pattern::constant("foo").alphabet(), indexset!{'f', 'o'});
    /// assert_eq!(Pattern::empty().alphabet(), indexset!{});
    /// assert_eq!(Pattern::variable(&Variable::temp(Sort::String)).alphabet(), indexset!{});
    /// ```
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
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::{Pattern, Symbol};
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert_eq!(Pattern::constant("foo").first(), Some(&Symbol::Constant('f')));
    /// assert_eq!(Pattern::empty().first(), None);
    /// let v = Variable::temp(Sort::String);
    /// assert_eq!(Pattern::variable(&v).first(), Some(&Symbol::Variable(v)));
    /// ```
    pub fn first(&self) -> Option<&Symbol> {
        self.symbols.first()
    }

    /// Returns the last symbol of the pattern, if it exists.
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::{Pattern, Symbol};
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert_eq!(Pattern::constant("foo").last(), Some(&Symbol::Constant('o')));
    /// assert_eq!(Pattern::empty().last(), None);
    /// let v = Variable::temp(Sort::String);
    /// assert_eq!(Pattern::variable(&v).last(), Some(&Symbol::Variable(v)));
    /// ```
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

    /// Reverses the pattern.
    ///
    /// # Example
    /// ```
    /// use satstr::model::constraints::Pattern;
    /// use satstr::model::{Variable, Sort};
    ///
    /// assert_eq!(Pattern::constant("foo").reversed(), Pattern::constant("oof"));
    /// assert_eq!(Pattern::empty().reversed(), Pattern::empty());
    /// let var = Variable::temp(Sort::String);
    /// let pattern = Pattern::constant("rab").append_var(&var).append_word("oof").clone();
    /// assert_eq!(pattern.reversed(), Pattern::constant("foo").append_var(&var).append_word("bar").clone());
    /// ```
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
        Self::new(self.rhs.reversed(), self.lhs.reversed())
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

/// Represents a constraint on a pattern to be contained in a regular language, given by a regular expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RegularConstraint {
    /// The regular expression. TODO: replace with Regex from regex crate
    re: ReTerm,
    /// The variable that is constrained by the regular expression.
    pattern: Pattern,
}

/* Evaluation */

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

/* Arbitrary */

use quickcheck;

impl Arbitrary for Symbol {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let choices = &[
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Constant(char::arbitrary(g)),
            Symbol::Variable(Variable::temp(Sort::String)),
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

    use crate::model::terms::{ReTerm, StringTerm};
    use crate::model::{Sort, Variable};

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
    fn pattern_empty_len_zero_equiv(pat: Pattern) {
        assert_eq!(pat.is_empty(), pat.len() == 0);
    }

    #[quickcheck]
    fn pattern_reverse_reverse_is_identity(pat: Pattern) -> bool {
        pat == pat.reversed().reversed()
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
