use std::collections::HashMap;

use cadical::Solver;
use indexmap::IndexSet;

use crate::{
    abstraction::Definition,
    bounds::Bounds,
    context::Context,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        EncodingResult, LiteralEncoder,
    },
    repr::ir::{Literal, VarSubstitution},
    sat::{nlit, pvar, PVar},
};

pub struct ProblemEncoder {
    /// The probe variable for each literal. These are used to check which literals failed, i.e., the encoding of which literals are part of the unsat core.
    probes: HashMap<Literal, PVar>,

    encoders: HashMap<Literal, Box<dyn LiteralEncoder>>,
    domain_encoder: DomainEncoder,
}

impl ProblemEncoder {
    pub fn new(alphabet: IndexSet<char>) -> Self {
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
        ctx: &Context,
    ) -> EncodingResult {
        // INPUT: BOUNDS
        // Encode the domain
        let mut res = self.domain_encoder.encode(bounds, ctx);

        // TODO: Instead let domain_encoder return the encoding of the domain or an Rc<DomainEncoding>
        let dom = self.domain_encoder.encoding().clone();
        // Encode all definitions
        for def in defs.iter() {
            let cnf = self.encode_def(def, bounds, &dom);
            res.extend(cnf);
        }

        res
    }

    fn encode_def(
        &mut self,
        def: &Definition,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> EncodingResult {
        let atom = def.atom();

        // Check if atom is regex and definition is equivalence, then use specialized encoding

        let mut res = EncodingResult::empty();
        let (probe, encoder) = if def.is_pos() {
            // Convert to literal. Cloning is cheap, because the atom is wrapped in an Rc.
            let lit = Literal::Positive(atom.clone());
            let probe = *self.probes.entry(lit.clone()).or_insert_with(|| pvar());
            let enc = self.get_encoder(&lit);
            (probe, enc)
        } else {
            // Convert to literal. Cloning is cheap, because the atom is wrapped in an Rc.
            let lit = Literal::Negative(atom.clone());
            let probe = *self.probes.entry(lit.clone()).or_insert_with(|| pvar());
            let enc = self.get_encoder(&lit);
            (probe, enc)
        };
        let mut encoding = encoder.encode(bounds, dom);

        // Add probe to every clause
        encoding
            .as_mut()
            .unwrap()
            .iter_clauses_mut()
            .for_each(|cl| cl.push(nlit(probe)));
        res.extend(encoding.unwrap());

        res
    }

    fn get_encoder(&mut self, lit: &Literal) -> &mut Box<dyn LiteralEncoder> {
        if self.encoders.get(lit).is_none() {
            // Create new encoder
            // self.encoders.insert(lit.clone(), Box::new(RegexEncoder::new()));
        }
        self.encoders.get_mut(lit).unwrap()
    }

    /// Returns the failed literals.
    pub fn get_failed_literals(&self, solver: &Solver) -> Vec<Literal> {
        todo!()
    }

    /// Blocks the assignment of the given substitution.
    /// Returns the CNF encoding of the blocked assignment.
    pub fn block_assignment(&self, sub: &VarSubstitution) {
        todo!()
    }

    /// Returns the model of the current assignment.
    pub fn get_model(&self, solver: &Solver, ctx: &Context) -> Option<VarSubstitution> {
        todo!()
    }
}
