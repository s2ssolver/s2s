mod canonicalize;
mod complements;
mod compress;

mod ite;
mod simp;
//mod simp;

use std::time::Instant;

use crate::{
    node::{error::NodeError, normal::to_nnf, Node, NodeManager, VarSubstitution},
    SolverOptions,
};
pub use canonicalize::canonicalize;

use compress::RangeCompressor;
use simp::Simplifier;
//use simp::Simplifier;

#[derive(Default)]
pub struct Preprocessor {
    subs: VarSubstitution,
}

impl Preprocessor {
    pub fn apply(
        &mut self,
        root: &Node,
        options: &SolverOptions,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        // first we need to get rid of the ITEs
        let mut ite_handler = ite::ITEHandler::default();
        let ite_elim = ite_handler.elim_ite(root, mngr);
        // Convert to NNF
        let mut new_root = to_nnf(&ite_elim, mngr);

        log::debug!("After ITE elimination:\n{}", new_root);

        if options.simplify {
            // Simplify the formula
            new_root = self.simplify(&new_root, options.preprocess_extra_passes, mngr);
        }

        let t = Instant::now();
        let mut compressor = RangeCompressor::default();
        new_root = compressor.compress(&new_root, mngr);
        log::debug!("Compressed formula in {:?}", t.elapsed());
        log::debug!("Compressed formula: {}", new_root);

        Ok(new_root)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let mut result = root.clone();

        let simplifier = Simplifier::default();
        let simp_res = simplifier.apply(&result, passes, mngr);
        let subs = simp_res.subs;
        result = to_nnf(&simp_res.node, mngr);

        for sub in subs {
            self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), mngr);
        }

        result
    }

    pub fn applied_substitutions(&self) -> &VarSubstitution {
        &self.subs
    }
}
