use std::fmt::Display;

use crate::{
    context::Context,
    domain::Domain,
    ir::{Atom, Literal, RegularConstraint},
};

use self::{boolvar::BoolVarEncoder, domain::DomainEncoding, linear::MddEncoder};

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
use re::build_inre_encoder;
use rustsat::{
    clause,
    instances::Cnf,
    types::{Clause, Lit},
};
use rustsat_cadical::CaDiCaL;
use smt_str::SmtChar;

/// The character used to represent unused positions
/// We use the maximum character allowed by the SMT-LIB standard
/// TODO: This is unsound if this character is used in the input.
const LAMBDA: SmtChar = SmtChar::MAX;

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

    pub fn not_epsi_free() -> Self {
        Self::new("NFA must be epsilon-free")
    }
}
impl Display for EncodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Encoding error: {}", self.msg)
    }
}

/// This trait is implemented by structs that can be used to record the encoding of a problem.
pub trait EncodingSink {
    /// Adds a clause to the encoding
    fn add_clause(&mut self, clause: Clause);

    fn add_binary(&mut self, a: Lit, b: Lit) {
        self.add_clause(clause![a, b]);
    }

    fn add_unit(&mut self, a: Lit) {
        self.add_clause(clause![a]);
    }

    /// Adds a clause to the encoding
    fn add_cnf(&mut self, cnf: Cnf) {
        for clause in cnf {
            self.add_clause(clause);
        }
    }

    /// Adds an assumption to the encoding
    fn add_assumption(&mut self, assumption: Lit);
}

/// This trait is implemented by structs that encode predicates. It is a general trait that is
/// subtyped for specific predicates.
/// Moreover, it serves as an indicator of whether or not the encoder performs an incremental encoding of the problem, when called with increased variable bounds.
/// If all encoders used to solver the problem are incremental, then the IPASIR interface of
/// the SAT solver will lead to a speedup.
///
/// Note that if an incremental encoder can be used in a non-incremental way by simply resetting its state when updating the bounds.
pub trait EncodeLiteral {
    /// Returns true if the encoder performs incremental encoding.
    fn _is_incremental(&self) -> bool {
        unimplemented!()
    }
    /// Resets the encoder to the initial state.
    /// After calling this functions, the next call to the `encode` function will completely re-encode the problem with the provided bounds.
    /// This has no effect on non-incremental encoders.
    fn _reset(&mut self) {
        unimplemented!()
    }

    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError>;

    fn print_debug(&self, _: &CaDiCaL) {}
}

#[allow(clippy::large_enum_variant)]
pub enum LiteralEncoder {
    BoolVar(BoolVarEncoder),
    NFAEncoder(re::NFAEncoder),
    WeqEncode(equation::WEQEncoder),
    LinearEncode(MddEncoder),
}

pub fn get_encoder(lit: &Literal, ctx: &mut Context) -> Result<LiteralEncoder, EncodingError> {
    let pol = lit.polarity();
    let e = match lit.atom().as_ref() {
        Atom::Boolvar(v) => LiteralEncoder::BoolVar(BoolVarEncoder::new(v, pol)),
        Atom::InRe(inre) => LiteralEncoder::NFAEncoder(build_inre_encoder(inre, pol, ctx)),
        Atom::WordEquation(weq) => LiteralEncoder::WeqEncode(equation::get_encoder(weq, pol)),
        Atom::FactorConstraint(rfc) => {
            // Right now, we cast it into a regular constraint
            log::warn!("Specialized encodings for regular factor constraints are not implemented yet. Casting to regular constraint.");
            let re = rfc.as_regex(ctx);
            let inre = RegularConstraint::new(rfc.of().clone(), re);
            LiteralEncoder::NFAEncoder(build_inre_encoder(&inre, pol, ctx))
        }
        Atom::Linear(lc) => LiteralEncoder::LinearEncode(MddEncoder::new(lc.clone(), pol)),
        Atom::True | Atom::False => return Err(EncodingError::new("Not canonical")),
    };
    Ok(e)
}

impl EncodeLiteral for LiteralEncoder {
    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        match self {
            LiteralEncoder::BoolVar(ref mut e) => e.encode(dom, dom_enc, sink),
            LiteralEncoder::NFAEncoder(ref mut e) => e.encode(dom, dom_enc, sink),
            LiteralEncoder::WeqEncode(ref mut e) => e.encode(dom, dom_enc, sink),
            LiteralEncoder::LinearEncode(ref mut e) => e.encode(dom, dom_enc, sink),
        }
    }

    fn _is_incremental(&self) -> bool {
        match self {
            LiteralEncoder::BoolVar(ref e) => e._is_incremental(),
            LiteralEncoder::NFAEncoder(ref e) => e._is_incremental(),
            LiteralEncoder::WeqEncode(ref e) => e._is_incremental(),
            LiteralEncoder::LinearEncode(ref e) => e._is_incremental(),
        }
    }

    fn _reset(&mut self) {
        match self {
            LiteralEncoder::BoolVar(ref mut e) => e._reset(),
            LiteralEncoder::NFAEncoder(ref mut e) => e._reset(),
            LiteralEncoder::WeqEncode(ref mut e) => e._reset(),
            LiteralEncoder::LinearEncode(ref mut e) => e._reset(),
        }
    }

    fn print_debug(&self, s: &CaDiCaL) {
        match self {
            LiteralEncoder::BoolVar(ref e) => e.print_debug(s),
            LiteralEncoder::NFAEncoder(ref e) => e.print_debug(s),
            LiteralEncoder::WeqEncode(ref e) => e.print_debug(s),
            LiteralEncoder::LinearEncode(ref e) => e.print_debug(s),
        }
    }
}

/// The result of an encoding.
/// It can be either a CNF encoding of the problem or a trivial encoding.
/// The trivial encoding is either unsat or sat.
/// The CNF encoding is a conjunction of clauses.
/// The assumptions are the literals that are assumed to be true.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum EncodingResult {
    /// The CNF encoding of the problem
    Cnf(Cnf, IndexSet<Lit>),
    /// The encoding is trivially valid or unsat
    Trivial(bool),
}

impl Default for EncodingResult {
    fn default() -> Self {
        EncodingResult::empty()
    }
}

#[allow(dead_code)]
impl EncodingResult {
    pub fn empty() -> Self {
        EncodingResult::Cnf(Cnf::new(), IndexSet::new())
    }

    /// Conjunctive normal form with no assumptions
    pub fn cnf(cnf: Cnf) -> Self {
        EncodingResult::Cnf(cnf, IndexSet::new())
    }

    /// Empty CNF with a single assumption
    pub fn assumption(assumption: Lit) -> Self {
        let mut asm = IndexSet::new();
        asm.insert(assumption);
        EncodingResult::Cnf(Cnf::new(), asm)
    }

    pub fn add_clause(&mut self, clause: Clause) {
        match self {
            EncodingResult::Cnf(ref mut clauses, _) => clauses.add_clause(clause),
            EncodingResult::Trivial(true) => {
                let mut cnf = Cnf::with_capacity(1);
                cnf.add_clause(clause);
                *self = EncodingResult::cnf(cnf);
            }
            EncodingResult::Trivial(false) => {}
        }
    }

    pub fn add_assumption(&mut self, assumption: Lit) {
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

    pub fn assumptions(&self) -> IndexSet<Lit> {
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
                EncodingResult::Cnf(cnf_other, asm_other) => {
                    cnf.extend(cnf_other);
                    asms.extend(asm_other);
                }
                EncodingResult::Trivial(false) => *self = other,
                EncodingResult::Trivial(true) => {}
            },
            EncodingResult::Trivial(true) => *self = other,
            EncodingResult::Trivial(false) => {}
        }
    }

    pub fn into_inner(self) -> (Cnf, IndexSet<Lit>) {
        match self {
            EncodingResult::Cnf(cnf, asms) => (cnf, asms),
            EncodingResult::Trivial(_) => (Cnf::new(), IndexSet::new()),
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

#[derive(Default)]
#[cfg(test)]
pub(crate) struct ResultSink {
    /// The result of the encoding
    result: EncodingResult,
}

#[cfg(test)]
impl EncodingSink for ResultSink {
    fn add_clause(&mut self, clause: Clause) {
        self.result.add_clause(clause);
    }

    fn add_assumption(&mut self, assumption: Lit) {
        self.result.add_assumption(assumption);
    }
}
#[cfg(test)]
impl ResultSink {
    /// Returns the result of the encoding
    pub fn result(self) -> EncodingResult {
        self.result
    }
}
