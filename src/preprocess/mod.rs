use indexmap::IndexSet;

mod canonicalize;
mod elim;
mod rewrite;
mod simp;

use crate::node::{error::NodeError, normal::to_nnf, Node, NodeManager, NodeSubstitution};
pub use canonicalize::canonicalize;
use elim::EliminateEntailed;
use rewrite::Rewriter;
use simp::Simplifier;

#[derive(Default)]
pub struct Preprocessor {
    subs: NodeSubstitution,
}

impl Preprocessor {
    pub fn apply(
        &mut self,
        root: &Node,
        passes: usize,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        // convert to nnf
        let nnf = to_nnf(root, mngr);
        // simplify
        let simped = self.simplify(&nnf, passes, mngr);
        log::debug!("Simplified:\n{}", simped);
        Ok(simped)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let mut rewriter = Rewriter::default();
        let mut simplifier = Simplifier::default();

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
            if let Some(new_node) = rewriter.rewrite(&result, 10, mngr) {
                applied = true;
                result = to_nnf(&new_node, mngr);
                for (old, new) in rewriter.applied() {
                    log::debug!("Rewrite: {} -> {}", old, new);
                }
            }
            if let Some(new_node) = simplifier.simplify(&result, 10, mngr) {
                applied = true;
                result = new_node;
                for sub in simplifier.applied() {
                    self.subs = std::mem::take(&mut self.subs).compose(sub.clone(), mngr);
                }
            }
            if !applied {
                break;
            }
        }
        result
    }

    pub fn applied_substitutions(&self) -> &NodeSubstitution {
        &self.subs
    }
}
