use std::collections::HashMap;

use cadical::Solver;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    abstraction::Definition,
    bounds::Bounds,
    context::Context,
    encode::{
        domain::{DomainEncoder, DomainEncoding},
        ConstraintEncoder, EncodingResult,
    },
    repr::ir::{Literal, VarSubstitution},
    sat::{pvar, Cnf, CnfA, PVar},
};

pub struct ProblemEncoder {
    /// The probe variable for each literal. These are used to check which literals failed, i.e., the encoding of which literals are part of the unsat core.
    probes: HashMap<Literal, PVar>,

    encoders: HashMap<Literal, Box<dyn ConstraintEncoder>>,
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

    pub fn encode(&mut self, defs: &[Definition], bounds: &Bounds, ctx: &Context) -> CnfA {
        // INPUT: BOUNDS
        // Encode the domain
        let mut res = match self.domain_encoder.encode(bounds, ctx) {
            EncodingResult::Cnf(cnf, asm) => CnfA::new(cnf, asm.into_iter().collect_vec()),
            EncodingResult::Trivial(_) => todo!(),
        };

        // Encode all definitions

        for def in defs.iter() {
            let cnf = self.encode_def(def, bounds);
            res.extend(cnf);
        }

        res
    }

    fn encode_def(&mut self, def: &Definition, bounds: &Bounds) -> CnfA {
        let atom = def.atom();

        // Check if atom is regex and definition is equivalence, then use specialized encoding
        let dom = self.domain_encoder.encoding();
        if def.is_pos() {
            // Convert to literal. Cloning is cheap, because the atom is wrapped in an Rc.
            let lit = Literal::Positive(atom.clone());
            let mut enc = self.get_encoder(&lit);
            let probe = self.probes.entry(lit.clone()).or_insert_with(|| pvar());
            enc.encode(bounds, dom)
            // Add probe to every clause
        }
        if def.is_neg() {
            // Convert to literal. Cloning is cheap, because the atom is wrapped in an Rc.
            let lit = Literal::Negative(atom.clone());
            let mut enc = self.get_encoder(&lit);
            let probe = self.probes.entry(lit.clone()).or_insert_with(|| pvar());
            enc.encode(bounds, dom)
            // Add probe to every clause
        }

        // OUTPUT: CNF with Assumptions
        todo!()
    }

    fn get_encoder(&mut self, lit: &Literal) -> &mut Box<dyn ConstraintEncoder> {
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
    pub fn get_model(&self, solver: &Solver) -> Option<VarSubstitution> {
        todo!()
    }
}
