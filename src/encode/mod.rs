use std::{fmt::Display, ops::Index, slice::Iter};

use crate::{
    bounds::Bounds,
    error::Error,
    model::{
        constraints::{Pattern, Symbol},
        Variable,
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

mod boolvar;

/// Encoder for regular constraints
mod re;

/// Encoder for linear constraints
mod linear;

pub use boolvar::BoolVarEncoder;
pub use equation::{AlignmentEncoder, IWoorpjeEncoder, WoorpjeEncoder, WordEquationEncoder};
use indexmap::IndexSet;
pub use linear::MddEncoder;
pub use re::build_re_encoder;

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
    fn fill(pattern: &Pattern, bounds: &Bounds) -> Self {
        Self {
            positions: Self::convert(pattern, bounds),
        }
    }

    fn convert(pattern: &Pattern, bounds: &Bounds) -> Vec<FilledPos> {
        let mut positions = vec![];
        for symbol in pattern.symbols() {
            match symbol {
                Symbol::Constant(c) => positions.push(FilledPos::Const(*c)),
                Symbol::Variable(v) => {
                    let len_var = &v.len_var().unwrap();
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

    pub fn clear_assumptions(&mut self) {
        match self {
            EncodingResult::Cnf(_, ref mut asms) => {
                asms.clear();
            }
            EncodingResult::Trivial(_) => {}
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

    pub fn assumptions(&self) -> IndexSet<PLit> {
        match self {
            EncodingResult::Cnf(_, asms) => asms.clone(),
            EncodingResult::Trivial(_) => IndexSet::new(),
        }
    }

    /// Returns the number of clauses in the encoding, not counting assumptions
    pub fn clauses(&self) -> usize {
        match self {
            EncodingResult::Cnf(cnf, _) => cnf.len(),
            EncodingResult::Trivial(_) => 0,
        }
    }

    /// Returns an iterator over mutable references of the clauses in the encoding
    /// If the encoding is trivial, returns an empty iterator
    pub fn iter_clauses_mut(&mut self) -> impl Iterator<Item = &mut Clause> {
        match self {
            EncodingResult::Cnf(cnf, _) => cnf.iter_mut(),
            EncodingResult::Trivial(_) => [].iter_mut(),
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

impl Display for EncodingResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EncodingResult::Cnf(cnf, assmp) => {
                for clause in cnf {
                    writeln!(f, "{:?}", clause)?;
                }
                write!(f, "c assumptions: ")?;
                for asm in assmp {
                    write!(f, "{} ", asm)?;
                }
                writeln!(f)
            }
            EncodingResult::Trivial(v) => {
                write!(f, "c trivially {}", if *v { "sat" } else { "unsat" })
            }
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
pub trait ConstraintEncoder {
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
    ) -> Result<EncodingResult, Error>;

    fn print_debug(&self, _solver: &cadical::Solver, _dom: &DomainEncoding) {}
}
