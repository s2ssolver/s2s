use crate::{
    node::{
        canonical::canonicalize, error::NodeError, normal::to_nnf, Node, NodeManager,
        NodeSubstitution,
    },
    rewrite::Rewriter,
    simp_new::Simplifier,
};

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
        let simplified = self.simplify(&nnf, passes, mngr);
        // canonicalize
        canonicalize(simplified, mngr)
    }

    fn simplify(&mut self, root: &Node, passes: usize, mngr: &mut NodeManager) -> Node {
        let mut rewriter = Rewriter::default();
        let mut simplifier = Simplifier::default();

        let mut result = root.clone();

        for _ in 0..passes {
            let mut applied = false;
            if let Some(new_node) = rewriter.rewrite(&result, 10, mngr) {
                applied = true;
                result = new_node;
                for (old, new) in rewriter.applied() {
                    log::debug!("Rewrite: {} -> {}", old, new);
                }
            }
            if let Some(new_node) = simplifier.simplify(&result, 1, mngr) {
                applied = true;
                result = new_node;
                for sub in simplifier.applied() {
                    log::debug!("Simplified: {}", sub);
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
