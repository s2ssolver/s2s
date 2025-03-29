use std::{ops::Neg, rc::Rc, time::Instant};

use crate::{
    abstraction::LitDefinition,
    alphabet::Alphabet,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        get_encoder, EncodeLiteral, EncodingError, EncodingResult, EncodingSink, LiteralEncoder,
    },
    node::{
        canonical::{AssignedValue, Assignment, Literal},
        NodeManager,
    },
    sat::{nlit, plit, pvar, PVar},
};
use indexmap::{IndexMap, IndexSet};
use rustsat::solvers::Solve;
use rustsat::{clause, types::Lit};
use rustsat::{solvers::SolveIncremental, types::Clause};
use rustsat_cadical::CaDiCaL;

use crate::domain::Domain;

/// A probe is a set of assumptions that determine whether the encoding of the literal is part of the unsat core.
/// It consists of a probe variable and the assumptions that were used to encode the literal.
/// The probe variable is added to all clauses in negated form and assumed to be true.
/// If the probe variable or any of the assumptions introduced by the encoding `failed`, the literal is part of the unsat core.
struct FailedProbe {
    // The probe variable for the literal, which is added to all clauses in negated form and assumed to be true.
    probe: PVar,
    // The assumptions that were used to encode the literal.
    assumptions: IndexSet<Lit>,
}
impl Default for FailedProbe {
    fn default() -> Self {
        Self {
            probe: pvar(),
            assumptions: IndexSet::new(),
        }
    }
}
impl FailedProbe {
    /// Sets the assumptions introduced by the encoding of the literal.
    pub fn set_assumptions(&mut self, assumptions: IndexSet<Lit>) {
        self.assumptions = assumptions;
    }

    pub fn probe_var(&self) -> PVar {
        self.probe
    }

    /// Returns an iterator over all probes. If one of the probes failed, the literal is part of the unsat core.
    pub fn iter(&self) -> impl IntoIterator<Item = Lit> + '_ {
        self.assumptions
            .iter()
            .copied()
            .chain(std::iter::once(plit(self.probe)))
    }
}

/// Encodes a set of definitions into CNF.
pub struct DefintionEncoder {
    /// The probe variable for each literal. These are used to check which literals failed, i.e., the encoding of which literals are part of the unsat core.
    probes: IndexMap<LitDefinition, FailedProbe>,

    encoders: IndexMap<Literal, LiteralEncoder>,
    domain_encoder: DomainEncoder,
}

impl DefintionEncoder {
    pub fn new(alphabet: Rc<Alphabet>) -> Self {
        Self {
            probes: IndexMap::new(),
            encoders: IndexMap::new(),
            domain_encoder: DomainEncoder::new(alphabet),
        }
    }

    pub fn encode(
        &mut self,
        defs: impl Iterator<Item = LitDefinition> + Clone,
        bounds: &Domain,
        cadical: &mut CaDiCaL<'static, 'static>,
        mngr: &mut NodeManager,
    ) -> Result<Vec<Lit>, EncodingError> {
        // INPUT: BOUNDS

        let t = Instant::now();

        let mut sink = CadicalEncodingSink::new(cadical);

        // Encode the domain
        let mut nclauses = sink.nclauses;
        self.domain_encoder.encode(bounds, &mut sink);
        let mut assumptions = std::mem::take(&mut sink.assumptions);

        log::debug!(
            "Encoded domain ({} clauses, {:?})",
            sink.nclauses - nclauses,
            t.elapsed()
        );

        // TODO: Instead let domain_encoder return the encoding of the domain or an Rc<DomainEncoding>
        let dom = self.domain_encoder.encoding().clone();

        // Encode all definitions
        for def in defs {
            let t = Instant::now();
            sink.clear_sub();
            sink.clear_assumptions();
            nclauses = sink.nclauses;
            let lit_assumptions = self.encode_def(&def, bounds, &dom, mngr, &mut sink)?;
            assumptions.extend(lit_assumptions);
            log::info!(
                "Encoded {} ({} clauses, {:?})",
                def,
                sink.nclauses - nclauses,
                t.elapsed()
            );
        }

        Ok(assumptions.into_iter().collect())
    }

    fn encode_def(
        &mut self,
        def: &LitDefinition,
        bounds: &Domain,
        dom: &DomainEncoding,
        mngr: &mut NodeManager,
        sink: &mut CadicalEncodingSink,
    ) -> Result<IndexSet<Lit>, EncodingError> {
        let lit = def.defined();
        let defining = def.defining();

        let probe_var = {
            let probe = self.probes.entry(def.clone()).or_default();
            probe.probe_var()
        };

        let sub = clause!(defining.neg(), nlit(probe_var));

        sink.set_sub(sub);

        self.get_encoder(lit, mngr).encode(bounds, dom, sink)?;

        let mut assumptions = std::mem::take(&mut sink.assumptions);

        self.probes
            .entry(def.clone())
            .or_default()
            .set_assumptions(assumptions.clone());

        // Add the probe variable to the assumptions
        assumptions.insert(plit(probe_var));
        sink.clear_sub();

        Ok(assumptions)
    }

    fn get_encoder(&mut self, lit: &Literal, mngr: &mut NodeManager) -> &mut LiteralEncoder {
        if self.encoders.get(lit).is_none() {
            // Create new encoder
            let encoder = get_encoder(lit, mngr).unwrap();
            self.encoders.insert(lit.clone(), encoder);
        }
        self.encoders.get_mut(lit).unwrap()
    }

    /// Returns the failed literals.
    pub fn get_failed_literals(&self, solver: &mut CaDiCaL) -> Vec<LitDefinition> {
        let mut failed = Vec::new();
        let core = solver.core().unwrap();
        for (lit, probes) in self.probes.iter() {
            for probe in probes.iter() {
                if core.contains(&-probe) {
                    failed.push(lit.clone());
                    break;
                }
            }
        }
        failed
    }

    /// Blocks the assignment of the given substitution.
    /// Returns the CNF encoding of the blocked assignment.
    pub fn block_assignment(&self, asn: &Assignment) -> EncodingResult {
        let mut res = EncodingResult::empty();
        for (var, val) in asn.iter() {
            match val {
                AssignedValue::String(w) => {
                    let mut clause = Clause::with_capacity(w.len());
                    for (i, c) in w.iter().enumerate() {
                        if let Some(x) = self.domain_encoder.encoding().string().get_sub(var, i, *c)
                        {
                            clause.add(nlit(x));
                        } else {
                            // Trivially Cannot be this word because either its outside alphabet or the word is too long
                            // So we can just break
                            break;
                        }
                    }
                    res.add_clause(clause);
                }
                AssignedValue::Int(i) => {
                    if let Some(x) = self.domain_encoder.encoding().int().get(var, *i) {
                        res.add_clause(clause![nlit(x)]);
                    }
                }
                AssignedValue::Bool(b) => {
                    if let Some(x) = self.domain_encoder.encoding().bool().get(var) {
                        if *b {
                            // must not be true
                            res.add_clause(clause![nlit(x)]);
                        } else {
                            // must not be false
                            res.add_clause(clause![plit(x)]);
                        }
                    }
                }
            }
        }
        res
    }

    /// Returns the model of the current assignment.
    pub fn get_model(&self, solver: &CaDiCaL) -> Assignment {
        self.domain_encoder.encoding().get_model(solver)
    }
}

pub(crate) struct CadicalEncodingSink<'a> {
    cadical: &'a mut CaDiCaL<'static, 'static>,
    assumptions: IndexSet<Lit>,

    sub: Option<Clause>,

    nclauses: usize,
}

impl<'a> CadicalEncodingSink<'a> {
    fn new(cadical: &'a mut CaDiCaL<'static, 'static>) -> Self {
        Self {
            cadical,
            assumptions: IndexSet::new(),
            sub: None,
            nclauses: 0,
        }
    }
}

impl CadicalEncodingSink<'_> {
    /// Sets the clause that is used to add all literals in the sub to the clause.
    pub fn set_sub(&mut self, sub: Clause) {
        self.sub = Some(sub);
    }

    pub fn clear_sub(&mut self) {
        self.sub = None;
    }

    fn clear_assumptions(&mut self) {
        self.assumptions.clear();
    }
}

impl<'a> EncodingSink for CadicalEncodingSink<'a> {
    fn add_clause(&mut self, mut clause: Clause) {
        if let Some(sub) = &self.sub {
            // Add all literals in sub to the clause
            for l in sub.iter() {
                clause.add(*l);
            }
        }
        self.nclauses += 1;
        self.cadical.add_clause(clause).unwrap();
    }

    fn add_assumption(&mut self, assumption: Lit) {
        self.assumptions.insert(assumption);
    }
}
