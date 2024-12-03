use std::{
    cmp::min,
    fmt::{Display, Formatter},
    rc::Rc,
};

use indexmap::IndexSet;
use regulaer::re::Regex;

use crate::node::{Sort, Sorted, Variable};

/// Represents a pattern symbol, which can be either a constant word or a variable.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Symbol {
    /// A constant character
    Constant(char),
    /// A variable
    Variable(Rc<Variable>),
}

impl Symbol {
    /// Returns true iff the symbol is a constant word.
    /// This is equivalent to `!is_variable()`.
    pub fn is_constant(&self) -> bool {
        matches!(self, Symbol::Constant(_))
    }

    /// Returns true iff the symbol is a constant word.
    /// This is equivalent to `!is_constant()`.
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

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Constant(c) => write!(f, "{}", c.escape_default()),
            Symbol::Variable(v) => write!(f, "{}", v),
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
    pub fn variable(var: Rc<Variable>) -> Self {
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

    pub fn as_variable(&self) -> Option<Rc<Variable>> {
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
        if n >= self.len() {
            Self::empty()
        } else {
            Self::new(self.symbols[n..].to_vec())
        }
    }

    /// Removes the last `n` symbols from the pattern and returns the result.
    /// If `n` is greater than the length of the pattern, the empty pattern is returned.
    pub fn strip_suffix(&self, n: usize) -> Self {
        if n >= self.len() {
            Self::empty()
        } else {
            Self::new(self.symbols[..self.len() - n].to_vec())
        }
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
    pub fn variables(&self) -> IndexSet<Rc<Variable>> {
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

    pub fn push_var(&mut self, var: Rc<Variable>) -> &mut Self {
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
    pub fn constant_prefix(&self) -> String {
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
    pub fn constant_suffix(&self) -> String {
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

    pub fn symbols(&self) -> impl Iterator<Item = &Symbol> {
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

impl FromIterator<char> for Pattern {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let symbols = iter.into_iter().map(Symbol::Constant).collect();
        Self::new(symbols)
    }
}

impl IntoIterator for Pattern {
    type Item = Symbol;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.symbols.into_iter()
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut word = String::new();
        let mut first = true;
        for symbol in &self.symbols {
            match symbol {
                Symbol::Constant(c) => {
                    if c.is_ascii() && !c.is_ascii_control() {
                        word.push(*c);
                    } else {
                        word.push_str(c.escape_unicode().to_string().as_str())
                    }
                }
                Symbol::Variable(variable) => {
                    if !word.is_empty() {
                        if !first {
                            write!(f, "⋅")?;
                        }
                        write!(f, "{}", word)?;
                        word.clear();
                        first = false;
                    }
                    if !first {
                        write!(f, "⋅")?;
                    }
                    write!(f, "{}", variable)?;
                    first = false;
                }
            }
        }
        if !word.is_empty() {
            if !first {
                write!(f, "⋅")?;
            }
            write!(f, "{}", word)?;
            word.clear();
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum WordEquation {
    ConstantEquality(String, String),
    VarEquality(Rc<Variable>, Rc<Variable>),
    VarAssignment(Rc<Variable>, String),
    General(Pattern, Pattern),
}

impl Display for WordEquation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            WordEquation::ConstantEquality(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
            WordEquation::VarEquality(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
            WordEquation::VarAssignment(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
            WordEquation::General(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
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
                Pattern::variable(lhs.clone())
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
            WordEquation::VarEquality(_, rhs) => Pattern::variable(rhs.clone()),
            WordEquation::General(_, rhs) => rhs.clone(),
        }
    }

    /// Returns the set of variables that occur in the word equation.
    pub fn variables(&self) -> IndexSet<Rc<Variable>> {
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
    pub fn reversed(&self) -> Self {
        Self::new(self.lhs().reversed(), self.rhs().reversed())
    }

    /// We call a word equation `proper` if it contains at least one side with both a variable and a constant.
    pub fn is_proper(&self) -> bool {
        (self.lhs().contains_constant() && !self.lhs().is_constant())
            || (self.rhs().contains_constant() && !self.rhs().is_constant())
    }
}

/// Represents a regular constraint, i.e. a pattern and a regular expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegularConstraint {
    lhs: Rc<Variable>,
    re: Regex,
}

impl RegularConstraint {
    /// Creates a new regular constraint from a pattern and a regular expression.
    pub fn new(lhs: Rc<Variable>, re: Regex) -> Self {
        Self { lhs, re }
    }

    /// Returns the left-hand side of the regular constraint.
    pub fn lhs(&self) -> &Rc<Variable> {
        &self.lhs
    }

    /// Returns the regular expression of the regular constraint.
    pub fn re(&self) -> &Regex {
        &self.re
    }
}

impl Display for RegularConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ∈ {}", self.lhs(), self.re())
    }
}

#[derive(Clone, Debug, Copy, Hash, PartialEq, Eq)]
pub enum FactorConstraintType {
    Prefix,
    Suffix,
    Contains,
}

/// Represents a constraint that enforces that a pattern is a prefix, suffix of another pattern or contains another pattern.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegularFactorConstraint {
    lhs: Rc<Variable>,
    rhs: String,
    typ: FactorConstraintType,
}
impl RegularFactorConstraint {
    /// Creates a new prefix of constraint from two patterns.
    fn new(lhs: Rc<Variable>, rhs: String, typ: FactorConstraintType) -> Self {
        Self { lhs, rhs, typ }
    }

    pub fn prefixof(lhs: Rc<Variable>, rhs: String) -> Self {
        Self::new(lhs, rhs, FactorConstraintType::Prefix)
    }

    pub fn suffixof(lhs: Rc<Variable>, rhs: String) -> Self {
        Self::new(lhs, rhs, FactorConstraintType::Suffix)
    }

    pub fn contains(lhs: Rc<Variable>, rhs: String) -> Self {
        Self::new(lhs, rhs, FactorConstraintType::Contains)
    }

    /// Returns the prefix of the prefix of constraint.
    pub fn lhs(&self) -> &Rc<Variable> {
        &self.lhs
    }

    /// Returns the pattern of the prefix of constraint.
    pub fn rhs(&self) -> &String {
        &self.rhs
    }

    pub fn typ(&self) -> FactorConstraintType {
        self.typ
    }
}

impl Display for RegularFactorConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.typ {
            FactorConstraintType::Prefix => write!(f, "{} ⊑ {}", self.lhs(), self.rhs()),
            FactorConstraintType::Suffix => write!(f, "{} ⊒ {}", self.lhs(), self.rhs()),
            FactorConstraintType::Contains => write!(f, "{} contains {}", self.lhs(), self.rhs()),
        }
    }
}
