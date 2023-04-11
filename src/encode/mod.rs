use std::{
    cmp::{max, min},
    collections::{HashMap, HashSet},
};

use crate::{
    model::{words::WordEquation, Variable},
    sat::{Cnf, PLit},
};

use self::substitution::SubstitutionEncoding;

/// Facilities for encoding cardinality constraints
mod card;
/// Encoder for word equations
pub mod equations;
/// Encoder for substitutions
pub mod substitution;

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

    pub fn set(&mut self, var: &Variable, bound: usize) {
        self.bounds.insert(var.clone(), bound);
    }

    pub fn set_default(&mut self, bound: usize) {
        self.default = bound;
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &usize)> {
        self.bounds.iter()
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

fn init_var_bounds(vars: HashSet<Variable>, init_value: usize) {
    todo!()
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

pub trait WordEquationEncoder: PredicateEncoder {
    fn new(equation: WordEquation) -> Self;
}
