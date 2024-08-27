use std::{collections::HashMap, time::Instant};

use cadical::Solver;

use crate::{
    abstraction::Definition,
    alphabet::Alphabet,
    bounds::Bounds,
    context::Context,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        get_encoder, EncodingError, EncodingResult, LiteralEncoder,
    },
    repr::ir::{Literal, VarSubstitution},
    sat::{nlit, plit, pvar, PLit, PVar},
};

pub struct ProblemEncoder {
    /// The probe variable for each literal. These are used to check which literals failed, i.e., the encoding of which literals are part of the unsat core.
    probes: HashMap<Literal, PVar>,

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
        defs: &[Definition],
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
            log::debug!("Encoded {} ({:?})", def, t.elapsed());
            res.extend(cnf);
        }

        Ok(res)
    }

    fn encode_def(
        &mut self,
        def: &Definition,
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

        let probe = *self.probes.entry(lit.clone()).or_insert_with(|| pvar());
        // Add probe to every clause
        encoding
            .iter_clauses_mut()
            .for_each(|cl| cl.push(nlit(probe)));
        // assert all probes
        encoding.add_assumption(plit(probe));
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
        self.probes
            .iter()
            .filter_map(|(lit, &probe)| {
                if solver.failed(plit(probe)) {
                    Some(lit.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Blocks the assignment of the given substitution.
    /// Returns the CNF encoding of the blocked assignment.
    pub fn block_assignment(&self, sub: &VarSubstitution) {
        todo!()
    }

    /// Returns the model of the current assignment.
    pub fn get_model(&self, solver: &Solver) -> VarSubstitution {
        self.domain_encoder.encoding().get_model(solver)
    }
}
