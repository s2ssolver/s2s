use std::{cmp::min, collections::HashMap, slice::Iter};

use crate::{
    model::{
        words::{Pattern, Symbol},
        Variable,
    },
    sat::Cnf,
};

use self::substitution::SubstitutionEncoding;

/// Facilities for encoding cardinality constraints
mod card;
/// Encoder for word equations
mod equation;
/// Encoder for substitutions
pub mod substitution;

pub use equation::{WoorpjeEncoder, WordEquationEncoder};

/// Bound for each variable
#[derive(Clone, Debug)]
pub struct VariableBounds {
    bounds: HashMap<Variable, usize>,
    default: usize,
}

impl VariableBounds {
    pub fn new(default: usize) -> Self {
        Self {
            bounds: HashMap::new(),
            default,
        }
    }

    pub fn get(&self, var: &Variable) -> usize {
        self.bounds.get(var).cloned().unwrap_or(self.default)
    }

    #[allow(dead_code)]
    pub fn set(&mut self, var: &Variable, bound: usize) {
        self.bounds.insert(var.clone(), bound);
    }

    #[allow(dead_code)]
    pub fn set_default(&mut self, bound: usize) {
        self.default = bound;
    }

    /// Updates the bounds of the variables by calling the given function on each bound, including the default bound.
    /// Additionally, an optional clamp can be provided to limit the maximum value of the bounds.
    /// If no clamp is provided, the bounds are limited by `usize::MAX`.
    /// Returns true if any bound was changed and false otherwise.
    pub fn update(&mut self, updater: impl Fn(usize) -> usize, clamp: Option<usize>) -> bool {
        let clamp = clamp.unwrap_or(usize::MAX);
        let mut any_changed = false;
        for (_, bound) in self.bounds.iter_mut() {
            let new_bound = min(updater(*bound), clamp);
            if new_bound != *bound {
                *bound = new_bound;
                any_changed = true;
            }
        }
        let new_default = min(updater(self.default), clamp);
        if new_default != self.default {
            self.default = new_default;
            any_changed = true;
        }
        any_changed
    }

    /// Doubles the bounds of all variables, including the default bound.
    /// The optional clamp can be used to limit the maximum value of the bounds.
    /// Returns true if any bound was changed and false otherwise.
    pub fn double(&mut self, clamp: Option<usize>) -> bool {
        self.update(|b| b * 2, clamp)
    }

    /// Updates the bounds of all variables such that they are the next square number greater than the current value.
    pub fn next_square(&mut self, clamp: Option<usize>) -> bool {
        self.update(|b| ((b as f64).sqrt() + 1f64).powi(2) as usize, clamp)
    }
}

impl std::fmt::Display for VariableBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (var, bound) in self.bounds.iter() {
            write!(f, ", {}: {}", var, bound)?;
        }
        write!(f, ", default: {}}}", self.default)?;
        Ok(())
    }
}

/// The character used to represent unused positions
const LAMBDA: char = char::REPLACEMENT_CHARACTER;

/// A position in a filled pattern.
/// Either a constant word or a position within a variable.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FilledPos {
    Const(char),
    FilledPos(Variable, usize),
}
/// A filled pattern is a pattern with a set of bounds on the variables.
/// Each position in the pattern is either a constant word or a position within a variable.
struct FilledPattern {
    positions: Vec<FilledPos>,
}

impl FilledPattern {
    fn fill(pattern: &Pattern, bounds: &VariableBounds) -> Self {
        Self {
            positions: Self::convert(pattern, bounds),
        }
    }

    fn convert(pattern: &Pattern, bounds: &VariableBounds) -> Vec<FilledPos> {
        let mut positions = vec![];
        for symbol in pattern.symbols() {
            match symbol {
                Symbol::Constant(c) => positions.push(FilledPos::Const(*c)),
                Symbol::Variable(v) => {
                    let len = bounds.get(v);
                    for i in 0..len {
                        positions.push(FilledPos::FilledPos(v.clone(), i))
                    }
                }
            }
        }
        positions
    }

    pub fn length(&self) -> usize {
        self.positions.len()
    }

    fn at(&self, i: usize) -> Option<&FilledPos> {
        self.positions.get(i)
    }

    #[allow(dead_code)]
    fn iter(&self) -> Iter<FilledPos> {
        self.positions.iter()
    }
}

pub enum EncodingResult {
    /// The CNF encoding of the problem
    Cnf(Cnf),
    /// The encoding is trivially valid or unsat
    Trivial(bool),
}

impl EncodingResult {
    pub fn empty() -> Self {
        EncodingResult::Cnf(vec![])
    }

    pub fn length(&self) -> usize {
        match self {
            EncodingResult::Cnf(cnf) => cnf.len(),
            EncodingResult::Trivial(_) => 0,
        }
    }

    /// Joins two encoding results, consumes the other one
    pub fn join(&mut self, other: EncodingResult) {
        match self {
            EncodingResult::Cnf(ref mut cnf) => match other {
                EncodingResult::Cnf(mut cnf_other) => cnf.append(&mut cnf_other),
                EncodingResult::Trivial(false) => *self = other,
                EncodingResult::Trivial(true) => {}
            },
            EncodingResult::Trivial(true) => *self = other,
            EncodingResult::Trivial(false) => {}
        }
    }
}

/// This trait is implemented by structs that encode predicates. It is a general trait that is
/// subtyped for specific predicates.
/// Moreover, it serves as an indicator of whether or not the encoder performs an incremental encoding of the problem, when called with increased variable bounds.
/// If all encoders used to solver the problem are incremental, then the IPASIR interface of
/// the SAT solver will lead to a speedup.
///
/// Note that if an incremental encoder can be used in a non-incremental way by simply resetting its state when updating the bounds.
pub trait PredicateEncoder {
    /// Returns true if the encoder performs incremental encoding.
    fn is_incremental(&self) -> bool;
    /// Resets the encoder to the initial state.
    /// After calling this functions, the next call to the `encode` function will completely re-encode the problem with the provided bounds.
    /// This has no effect on non-incremental encoders.
    fn reset(&self) -> bool;

    fn encode(
        &mut self,
        bounds: &VariableBounds,
        substitution: &SubstitutionEncoding,
    ) -> EncodingResult;
}
