use crate::{
    canonical::{canonicalize, Formula},
    node::{error::NodeError, normal::to_nnf, Node, NodeManager, NodeSubstitution},
    rewrite::Rewriter,
    simp::Simplifier,
};

#[derive(Default)]
pub struct Preprocessor {
    canonicalize_only: bool,
    subs: NodeSubstitution,
}

impl Preprocessor {
    pub fn no_simp() -> Self {
        Self {
            canonicalize_only: true,
            ..Default::default()
        }
    }

    pub fn apply(
        &mut self,
        root: &Node,
        passes: usize,
        mngr: &mut NodeManager,
    ) -> Result<Formula, NodeError> {
        // convert to nnf
        let nnf = to_nnf(root, mngr);
        // simplify
        let simplified = if self.canonicalize_only {
            nnf
        } else {
            let simped = self.simplify(&nnf, passes, mngr);
            log::debug!("Simplified:\n{}", simped);
            simped
        };
        // canonicalize
        canonicalize(&simplified, mngr)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let mut rewriter = Rewriter::default();
        let mut simplifier = Simplifier::default();

        let mut result = root.clone();

        let mut last_size = root.size();
        let mut pass = 0;

        while pass < passes || result.size() < last_size {
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

    pub fn applied_subsitutions(&self) -> &NodeSubstitution {
        &self.subs
    }
}
