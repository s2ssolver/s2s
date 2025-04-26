mod canonicalize;
mod complements;
mod compress;

mod guess;
mod ite;
mod simp;
//mod simp;

use std::time::Instant;

use crate::{
    node::{error::NodeError, normal::to_nnf, Node, NodeManager, VarSubstitution},
    Options,
};
pub use canonicalize::canonicalize;

use compress::RangeCompressor;
use guess::BoolVarGuesser;
use simp::Simplifier;
//use simp::Simplifier;

#[derive(Default)]
pub struct Preprocessor {
    subs: VarSubstitution,
    options: Options,
}

impl Preprocessor {
    pub fn new(options: Options) -> Self {
        Self {
            options,
            subs: VarSubstitution::default(),
        }
    }

    pub fn apply(&mut self, root: &Node, mngr: &mut NodeManager) -> Result<Node, NodeError> {
        // first we need to get rid of the ITEs
        let mut ite_handler = ite::ITEHandler::default();
        let ite_elim = ite_handler.elim_ite(root, mngr);
        // Convert to NNF
        let mut new_root = to_nnf(&ite_elim, mngr);

        log::debug!("After ITE elimination:\n{}", new_root);

        if self.options.simplify {
            // Simplify the formula
            new_root = self.simplify(&new_root, self.options.simp_max_passes, mngr);
        }
        if self.options.guess_bools {
            new_root = self.guess_bools(&new_root, mngr)
        }
        // ensure we are still in NNF
        new_root = to_nnf(&new_root, mngr);

        if self.options.compress {
            let t = Instant::now();
            new_root = self.range_compression(&new_root, mngr);
            log::debug!("Compressed formula in {:?}", t.elapsed());
            log::debug!("Compressed formula: {}", new_root);
        }

        Ok(new_root)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let simplifier = Simplifier::default();
        let simp_res = simplifier.apply(root, passes, mngr);

        for sub in simp_res.subs {
            self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), mngr);
        }

        simp_res.node
    }

    fn guess_bools(&mut self, root: &Node, mngr: &mut NodeManager) -> Node {
        // Guess Boolean vars
        let guesser = BoolVarGuesser::new(self.options.clone());
        let guessed = guesser.apply(root, mngr);

        for sub in guessed.subs {
            self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), mngr);
        }

        guessed.node
    }

    fn range_compression(&mut self, root: &Node, mngr: &mut NodeManager) -> Node {
        let mut compressor = RangeCompressor::default();
        compressor.compress(&root, mngr)
    }

    pub fn applied_substitutions(&self) -> &VarSubstitution {
        &self.subs
    }
}
