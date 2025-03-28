use std::{ops::Neg, rc::Rc, time::Instant};

use crate::{
    abstraction::LitDefinition,
    alphabet::Alphabet,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        get_encoder, EncodingError, EncodingResult, LiteralEncoder,
    },
    node::{
        canonical::{AssignedValue, Assignment, Literal},
        NodeManager,
    },
    sat::{nlit, plit, pvar, PVar},
};
use indexmap::{IndexMap, IndexSet};
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

    encoders: IndexMap<Literal, Box<dyn LiteralEncoder>>,
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
        mngr: &mut NodeManager,
    ) -> Result<EncodingResult, EncodingError> {
        // INPUT: BOUNDS

        let t = Instant::now();

        // Encode the domain
        let mut res = self.domain_encoder.encode(bounds);

        log::debug!("Encoded domain ({:?})", t.elapsed());

        // TODO: Instead let domain_encoder return the encoding of the domain or an Rc<DomainEncoding>
        let dom = self.domain_encoder.encoding().clone();
        // Encode all definitions
        for def in defs {
            let t = Instant::now();
            let cnf = self.encode_def(&def, bounds, &dom, mngr)?;
            res.extend(cnf);
            log::debug!("Encoded {} ({:?})", def, t.elapsed());
        }

        Ok(res)
    }

    fn encode_def(
        &mut self,
        def: &LitDefinition,
        bounds: &Domain,
        dom: &DomainEncoding,
        mngr: &mut NodeManager,
    ) -> Result<EncodingResult, EncodingError> {
        let lit = def.defined();
        let defining = def.defining();
        let mut encoding = self.get_encoder(lit, mngr).encode(bounds, dom)?;

        // Add -def var to every clause
        encoding.iter_clauses_mut().for_each(|cl| {
            cl.add(defining.neg());
        });

        let probe = self.probes.entry(def.clone()).or_default();
        probe.set_assumptions(encoding.assumptions().clone());
        let pvar = probe.probe_var();

        // Add -probe to every clause
        encoding
            .iter_clauses_mut()
            .for_each(|cl| cl.add(nlit(pvar)));
        // assert all probes
        encoding.add_assumption(plit(pvar));
        Ok(encoding)
    }

    fn get_encoder(
        &mut self,
        lit: &Literal,
        mngr: &mut NodeManager,
    ) -> &mut Box<dyn LiteralEncoder> {
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
