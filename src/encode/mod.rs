use std::{cmp::min, collections::HashMap, ops::Index, slice::Iter};

use crate::{
    bounds::Bounds,
    model::{
        words::{Pattern, Symbol},
        Sort, VarManager, Variable,
    },
    sat::{Clause, Cnf, PLit},
};

use self::domain::DomainEncoding;

/// Facilities for encoding cardinality constraints
mod card;
/// Encoder for substitutions
pub mod domain;
/// Encoder for word equations
mod equation;

/// Encoder for linear constraints
mod linear;

pub use equation::{BindepEncoder, IWoorpjeEncoder, WoorpjeEncoder, WordEquationEncoder};
use indexmap::IndexSet;
pub use linear::MddEncoder;

/// Maps each variable of sort `Int` to its domain given by a lower and upper bound.
#[derive(Clone, Debug)]
pub struct IntegerDomainBounds {
    bounds: HashMap<Variable, (isize, isize)>,
    default: (isize, isize),
}

impl IntegerDomainBounds {
    pub fn new(default: (isize, isize)) -> Self {
        Self {
            bounds: HashMap::new(),
            default,
        }
    }

    pub fn get(&self, var: &Variable) -> (isize, isize) {
        assert!(var.sort() == Sort::Int);
        self.bounds.get(var).cloned().unwrap_or(self.default)
    }

    pub fn get_upper(&self, var: &Variable) -> isize {
        self.get(var).1
    }

    #[allow(dead_code)]
    pub fn set(&mut self, var: &Variable, bound: (isize, isize)) {
        assert!(var.sort() == Sort::Int);
        self.bounds.insert(var.clone(), bound);
    }

    pub fn set_upper(&mut self, var: &Variable, bound: isize) {
        assert!(var.sort() == Sort::Int);
        let lower = self.get(var).0;
        self.bounds.insert(var.clone(), (lower, bound));
    }

    #[allow(dead_code)]
    pub fn set_default(&mut self, bound: (isize, isize)) {
        self.default = bound;
    }

    /// Returns true if the upper bounds of all variables are less or equal to the given value.
    #[allow(dead_code)]
    pub fn all_leq(&self, limit: isize) -> bool {
        if self.default.1 > limit {
            return false;
        }
        for (_var, bound) in self.bounds.iter() {
            if bound.1 > limit {
                return false;
            }
        }

        true
    }
}

impl std::fmt::Display for IntegerDomainBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (var, bound) in self.bounds.iter() {
            write!(f, ", {}: {:?}", var, bound)?;
        }
        write!(f, ", default: {:?}}}", self.default)?;
        Ok(())
    }
}

impl std::cmp::PartialEq for IntegerDomainBounds {
    fn eq(&self, other: &Self) -> bool {
        if self.default != other.default {
            return false;
        }
        // Check if all vars known by any of the bounds have the same bound
        let mut all_vars = IndexSet::new();
        all_vars.extend(self.bounds.keys());
        all_vars.extend(other.bounds.keys());
        for var in all_vars {
            if self.get(var) != other.get(var) {
                return false;
            }
        }
        true
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
    fn fill(pattern: &Pattern, bounds: &Bounds, var_manager: &VarManager) -> Self {
        Self {
            positions: Self::convert(pattern, bounds, var_manager),
        }
    }

    fn convert(pattern: &Pattern, bounds: &Bounds, var_manager: &VarManager) -> Vec<FilledPos> {
        let mut positions = vec![];
        for symbol in pattern.symbols() {
            match symbol {
                Symbol::Constant(c) => positions.push(FilledPos::Const(*c)),
                Symbol::Variable(v) => {
                    let len_var = var_manager.str_length_var(v).unwrap_or_else(|| {
                        panic!("Variable {} does not have a length variable", v)
                    });
                    let len = bounds.get_upper(len_var).unwrap() as usize;
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

impl Index<usize> for FilledPattern {
    type Output = FilledPos;

    fn index(&self, index: usize) -> &Self::Output {
        &self.positions[index]
    }
}

pub enum EncodingResult {
    /// The CNF encoding of the problem
    Cnf(Cnf, IndexSet<PLit>),
    /// The encoding is trivially valid or unsat
    Trivial(bool),
}

impl EncodingResult {
    pub fn empty() -> Self {
        EncodingResult::Cnf(vec![], IndexSet::new())
    }

    /// Conjunctive normal form with no assumptions
    pub fn cnf(cnf: Cnf) -> Self {
        EncodingResult::Cnf(cnf, IndexSet::new())
    }

    /// Empty CNF with a single assumption
    pub fn assumption(assumption: PLit) -> Self {
        let mut asm = IndexSet::new();
        asm.insert(assumption);
        EncodingResult::Cnf(vec![], asm)
    }

    pub fn add_clause(&mut self, clause: Clause) {
        match self {
            EncodingResult::Cnf(ref mut clauses, _) => clauses.push(clause),
            EncodingResult::Trivial(true) => *self = EncodingResult::cnf(vec![clause]),
            EncodingResult::Trivial(false) => {}
        }
    }

    pub fn add_assumption(&mut self, assumption: PLit) {
        match self {
            EncodingResult::Cnf(_, ref mut asms) => {
                asms.insert(assumption);
            }
            EncodingResult::Trivial(true) => {
                *self = EncodingResult::assumption(assumption);
            }
            EncodingResult::Trivial(false) => {}
        }
    }

    /// Returns the number of clauses in the encoding, not counting assumptions
    pub fn clauses(&self) -> usize {
        match self {
            EncodingResult::Cnf(cnf, _) => cnf.len(),
            EncodingResult::Trivial(_) => 0,
        }
    }

    /// Joins two encoding results, consumes the other one
    pub fn join(&mut self, other: EncodingResult) {
        match self {
            EncodingResult::Cnf(ref mut cnf, ref mut asms) => match other {
                EncodingResult::Cnf(mut cnf_other, asm_other) => {
                    cnf.append(&mut cnf_other);
                    asms.extend(asm_other);
                }
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
    fn reset(&mut self);

    fn encode(
        &mut self,
        bounds: &Bounds,
        substitution: &DomainEncoding,
        var_manager: &VarManager,
    ) -> EncodingResult;
}
