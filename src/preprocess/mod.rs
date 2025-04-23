mod canonicalize;
mod complements;
mod compress;

mod guess;
mod ite;
mod simp;
//mod simp;

use std::time::Instant;

use crate::{
    ast::{error::NodeError, normal::to_nnf, Node, VarSubstitution},
    context::Context,
    SolverOptions,
};
pub use canonicalize::canonicalize;

use compress::RangeCompressor;
use guess::BoolVarGuesser;
use simp::Simplifier;
//use simp::Simplifier;

#[derive(Default)]
pub struct Preprocessor {
    subs: VarSubstitution,
    options: SolverOptions,
}

impl Preprocessor {
    pub fn new(options: SolverOptions) -> Self {
        Self {
            options,
            subs: VarSubstitution::default(),
        }
    }

    pub fn apply(&mut self, root: &Node, ctx: &mut Context) -> Result<Node, NodeError> {
        // first we need to get rid of the ITEs
        let mut ite_handler = ite::ITEHandler::default();
        let ite_elim = ite_handler.elim_ite(root, ctx);
        // Convert to NNF
        let mut new_root = to_nnf(&ite_elim, ctx);

        log::debug!("After ITE elimination:\n{}", new_root);

        if self.options.simplify {
            // Simplify the formula
            new_root = self.simplify(&new_root, self.options.simp_max_passes, ctx);
        }
        if self.options.guess_bools {
            new_root = self.guess_bools(&new_root, ctx)
        }
        // ensure we are still in NNF
        new_root = to_nnf(&new_root, ctx);

        let t = Instant::now();
        let mut compressor = RangeCompressor::default();
        new_root = compressor.compress(&new_root, ctx);
        log::debug!("Compressed formula in {:?}", t.elapsed());
        log::debug!("Compressed formula: {}", new_root);

        Ok(new_root)
    }

    fn simplify(&mut self, root: &Node, passes: usize, ctx: &mut Context) -> Node {
        let simplifier = Simplifier::default();
        let simp_res = simplifier.apply(root, passes, ctx);

        for sub in simp_res.subs {
            self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), ctx);
        }

        simp_res.node
    }

    fn guess_bools(&mut self, root: &Node, ctx: &mut Context) -> Node {
        // Guess Boolean vars
        let guesser = BoolVarGuesser::new(self.options.clone());
        let guessed = guesser.apply(root, ctx);

        for sub in guessed.subs {
            self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), ctx);
        }

        guessed.node
    }

    pub fn applied_substitutions(&self) -> &VarSubstitution {
        &self.subs
    }
}
