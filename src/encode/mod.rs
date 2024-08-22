use std::{fmt::Display, ops::Index, slice::Iter};

use crate::{
    bounds::Bounds,
    context::Context,
    repr::{
        ir::{AtomType, Literal, Pattern, Symbol},
        Variable,
    },
    sat::{Clause, Cnf, PLit},
};

use self::{
    boolvar::BoolVarEncoder, domain::DomainEncoding, linear::MddEncoder, re::build_inre_encoder,
};

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

use indexmap::IndexSet;

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
    fn fill(pattern: &Pattern, bounds: &Bounds, ctx: &Context) -> Self {
        Self {
            positions: Self::convert(pattern, bounds, ctx),
        }
    }

    fn convert(pattern: &Pattern, bounds: &Bounds, ctx: &Context) -> Vec<FilledPos> {
        let mut positions = vec![];
        for symbol in pattern.symbols() {
            match symbol {
                Symbol::Constant(c) => positions.push(FilledPos::Const(*c)),
                Symbol::Variable(v) => {
                    let len_var = ctx.get_len_var(v).as_ref().clone();
                    let len = bounds.get_upper(&len_var).unwrap() as usize;
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
    pub fn extend(&mut self, other: EncodingResult) {
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

    pub fn into_inner(self) -> (Cnf, IndexSet<PLit>) {
        match self {
            EncodingResult::Cnf(cnf, asms) => (cnf, asms),
            EncodingResult::Trivial(_) => (vec![], IndexSet::new()),
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

#[derive(Debug, thiserror::Error)]
pub struct EncodingError {
    msg: String,
}
impl EncodingError {
    pub fn new(msg: &str) -> Self {
        Self {
            msg: msg.to_string(),
        }
    }
}
impl Display for EncodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Encoding error: {}", self.msg)
    }
}

/// This trait is implemented by structs that encode predicates. It is a general trait that is
/// subtyped for specific predicates.
/// Moreover, it serves as an indicator of whether or not the encoder performs an incremental encoding of the problem, when called with increased variable bounds.
/// If all encoders used to solver the problem are incremental, then the IPASIR interface of
/// the SAT solver will lead to a speedup.
///
/// Note that if an incremental encoder can be used in a non-incremental way by simply resetting its state when updating the bounds.
pub trait LiteralEncoder {
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
        ctx: &Context,
    ) -> Result<EncodingResult, EncodingError>;

    fn print_debug(&self, _solver: &cadical::Solver, _dom: &DomainEncoding) {}
}

pub fn get_encoder(
    lit: &Literal,
    ctx: &mut Context,
) -> Result<Box<dyn LiteralEncoder>, EncodingError> {
    let pol = lit.polarity();
    match lit.atom().get_type() {
        AtomType::BoolVar(v) => Ok(Box::new(BoolVarEncoder::new(v, pol))),
        AtomType::InRe(inre) => build_inre_encoder(inre, pol, ctx),
        AtomType::WordEquation(_) => todo!(),
        AtomType::PrefixOf(_) => todo!(),
        AtomType::SuffixOf(_) => todo!(),
        AtomType::Contains(_) => todo!(),
        AtomType::LinearConstraint(lc) => Box::new(MddEncoder::new(lc.clone())),
        AtomType::BoolConst(_) => todo!(),
        // Constraint::WordEquation(eq) => equation::get_encoder(eq),
        // Constraint::LinearConstraint(lc) => Box::new(MddEncoder::new(lc.clone())),
        // Constraint::RegularConstraint(rec) => ,
        // Constraint::BoolVarConstraint(v, pol) => Box::new(BoolVarEncoder::new(v.clone(), *pol)),
    }
}
