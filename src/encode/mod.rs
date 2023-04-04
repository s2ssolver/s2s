use std::collections::{HashMap, HashSet};

use crate::{
    model::{words::WordEquation, Variable},
    sat::Cnf,
};

use self::substitution::SubstitutionEncoding;

/// Facilities for encoding cardinality constraints
mod card;
/// Encoder for word equations
pub mod equations;
/// Encoder for substitutions
pub mod substitution;

/// Bound for each variable
type VariableBounds = HashMap<Variable, usize>;

/// The character used to represent unused positions
const LAMBDA: char = char::REPLACEMENT_CHARACTER;

fn init_var_bounds(vars: HashSet<Variable>, init_value: usize) {
    todo!()
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

    fn encode(&self, bounds: &VariableBounds, substitution: &SubstitutionEncoding) -> Cnf;
}

pub trait WordEquationEncoder: PredicateEncoder {
    fn new(equation: WordEquation) -> Self;
}
