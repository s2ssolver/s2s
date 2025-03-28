mod canonicalize;
mod complements;
mod compress;
mod elim;
mod ite;
mod rewrite;
//mod simp;

use std::time::Instant;

use crate::{
    node::{error::NodeError, normal::to_nnf, Node, NodeManager, VarSubstitution},
    SolverOptions,
};
pub use canonicalize::canonicalize;

use compress::RangeCompressor;
use elim::EliminateEntailed;
use rewrite::Rewriter;
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
        new_root = compress_ranges(&new_root, mngr);
        log::debug!("Compressed formula in {:?}", t.elapsed());
        log::debug!("Compressed formula: {}", new_root);

        Ok(new_root)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let mut result = root.clone();

        let mut last_size = root.size();
        let mut pass = 0;

        while pass < passes || result.size() < last_size {
            // First remove all non-entailed occurrences of entailed literals
            let mut lit_eliminator = EliminateEntailed::default();
            result = lit_eliminator.apply(result, mngr);

            if result.size() >= last_size {
                // we only count passes if we did not simplify
                pass += 1;
            }
            last_size = result.size();
            let mut applied = false;
            let mut rewriter = Rewriter::default();
            // Rewrite passes are cheaper than simplification passes, so we do them first and with a higher limit
            let new_node = rewriter.rewrite(&result, passes, mngr);
            if new_node != result {
                applied = true;
                result = to_nnf(&new_node, mngr);
            }

            if !applied {
                break;
            }
            for sub in rewriter.get_applied_subs() {
                self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), mngr);
            }
        }

        result
    }

    pub fn applied_substitutions(&self) -> &VarSubstitution {
        &self.subs
    }
}

pub fn compress_ranges(node: &Node, mngr: &mut NodeManager) -> Node {
    let mut compressor = RangeCompressor::default();
    compressor.compress(node, mngr)
}
