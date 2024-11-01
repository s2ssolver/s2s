use std::{collections::HashMap, time::Instant};

use cadical::Solver;
use indexmap::IndexSet;

use crate::{
    abstraction::DefinitionOld,
    alphabet::Alphabet,
    bounds::Bounds,
    context::Context,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        get_encoder, EncodingError, EncodingResult, LiteralEncoder,
    },
    ir::{Literal, VarSubstitution},
    sat::{nlit, plit, pvar, PLit, PVar},
};

/// A probe is a set of assumptions that determine whether the encoding of the literal is part of the unsat core.
/// It consists of a probe variable and the assumptions that were used to encode the literal.
/// The probe variable is added to all clauses in negated form and assumed to be true.
/// If the probe variable or any of the assumptions introduced by the encoding `failed`, the literal is part of the unsat core.
struct FailedProbe {
    // The probe variable for the literal, which is added to all clauses in negated form and assumed to be true.
    probe: PVar,
    // The assumptions that were used to encode the literal.
    assumptions: IndexSet<PLit>,
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
    pub fn set_assumptions(&mut self, assumptions: IndexSet<PLit>) {
        self.assumptions = assumptions;
    }

    pub fn probe_var(&self) -> PVar {
        self.probe
    }

    /// Returns an iterator over all probes. If one of the probes failed, the literal is part of the unsat core.
    pub fn iter(&self) -> impl IntoIterator<Item = PLit> + '_ {
        self.assumptions
            .iter()
            .copied()
            .chain(std::iter::once(plit(self.probe)))
    }
}

pub struct ProblemEncoder {
    /// The probe variable for each literal. These are used to check which literals failed, i.e., the encoding of which literals are part of the unsat core.
    probes: HashMap<Literal, FailedProbe>,

    encoders: HashMap<Literal, Box<dyn LiteralEncoder>>,
    domain_encoder: DomainEncoder,
}

impl ProblemEncoder {
    pub fn new(alphabet: Alphabet) -> Self {
        Self {
            probes: HashMap::new(),
            encoders: HashMap::new(),
            domain_encoder: DomainEncoder::new(alphabet),
        }
    }

    pub fn encode(
        &mut self,
        defs: &[DefinitionOld],
        bounds: &Bounds,
        ctx: &mut Context,
    ) -> Result<EncodingResult, EncodingError> {
        // INPUT: BOUNDS
        // Encode the domain
        let t = Instant::now();
        let mut res = self.domain_encoder.encode(bounds, ctx);
        log::debug!("Encoded domain ({:?})", t.elapsed());

        // TODO: Instead let domain_encoder return the encoding of the domain or an Rc<DomainEncoding>
        let dom = self.domain_encoder.encoding().clone();
        // Encode all definitions
        for def in defs.iter() {
            let t = Instant::now();
            let cnf = self.encode_def(def, bounds, &dom, ctx)?;
            res.extend(cnf);
            log::debug!("Encoded {} ({:?})", def, t.elapsed());
        }

        Ok(res)
    }

    fn encode_def(
        &mut self,
        def: &DefinitionOld,
        bounds: &Bounds,
        dom: &DomainEncoding,
        ctx: &mut Context,
    ) -> Result<EncodingResult, EncodingError> {
        let atom = def.atom();

        // Check if atom is regex and definition is equivalence, then use specialized encoding

        let mut res = EncodingResult::empty();

        if def.is_pos() {
            // def_var -> atom
            let lit = Literal::Positive(atom.clone());
            let def_lit = nlit(def.def_var());

            let encoding = self.encode_literal(&lit, def_lit, bounds, dom, ctx)?;
            res.extend(encoding);
        }

        if def.is_neg() {
            // -def_var -> -atom
            let lit = Literal::Negative(atom.clone());
            let def_lit = plit(def.def_var());

            let encoding = self.encode_literal(&lit, def_lit, bounds, dom, ctx)?;
            res.extend(encoding);
        }

        Ok(res)
    }

    fn encode_literal(
        &mut self,
        lit: &Literal,
        def: PLit,
        bounds: &Bounds,
        dom: &DomainEncoding,
        ctx: &mut Context,
    ) -> Result<EncodingResult, EncodingError> {
        let mut encoding = self.get_encoder(&lit, ctx).encode(bounds, dom)?;

        // Add -def var to every clause
        encoding.iter_clauses_mut().for_each(|cl| {
            cl.push(def);
        });

        let probe = self.probes.entry(lit.clone()).or_default();
        probe.set_assumptions(encoding.assumptions().clone());
        let pvar = probe.probe_var();

        // Add -probe to every clause
        encoding
            .iter_clauses_mut()
            .for_each(|cl| cl.push(nlit(pvar)));
        // assert all probes
        encoding.add_assumption(plit(pvar));
        Ok(encoding)
    }

    fn get_encoder(&mut self, lit: &Literal, ctx: &mut Context) -> &mut Box<dyn LiteralEncoder> {
        if self.encoders.get(lit).is_none() {
            // Create new encoder
            let encoder = get_encoder(lit, ctx).unwrap();
            self.encoders.insert(lit.clone(), encoder);
        }
        self.encoders.get_mut(lit).unwrap()
    }

    /// Returns the failed literals.
    pub fn get_failed_literals(&self, solver: &Solver) -> Vec<Literal> {
        let mut failed = Vec::new();
        for (lit, probes) in self.probes.iter() {
            for probe in probes.iter() {
                if solver.failed(probe) {
                    failed.push(lit.clone());
                    break;
                }
            }
        }
        failed
    }

    #[allow(dead_code)]
    pub(crate) fn print_debug(&self, solver: &Solver) {
        for (l, enc) in self.encoders.iter() {
            println!("Debug: {}", l);
            enc.print_debug(solver, self.domain_encoder.encoding());
        }
    }

    /// Blocks the assignment of the given substitution.
    /// Returns the CNF encoding of the blocked assignment.
    pub fn block_assignment(&self, _sub: &VarSubstitution) {
        todo!()
    }

    /// Returns the model of the current assignment.
    pub fn get_model(&self, solver: &Solver) -> VarSubstitution {
        self.domain_encoder.encoding().get_model(solver)
    }
}
