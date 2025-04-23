use indexmap::IndexSet;

use crate::ast::{get_entailed, Node};
use crate::context::{Context, Sorted};

/// Removes all other occurrences of an entailed literals from the formula by replacing them with `true` or `false`.
/// This is neither a simplification nor a rewrite rule, but an additional preprocessing step.
#[derive(Clone, Default)]
pub struct EliminateEntailed {
    // All nodes that have a non-entailed occurrence.
    entailed: IndexSet<Node>,
}

impl EliminateEntailed {
    fn occurrs_entailed(&self, node: &Node) -> bool {
        self.entailed.contains(node)
    }

    pub fn apply(&mut self, root: &Node, ctx: &mut Context) -> Node {
        self.entailed = get_entailed(root);
        self.apply_node(root, true, ctx)
    }

    fn apply_node(&self, node: &Node, entailed: bool, ctx: &mut Context) -> Node {
        if node.sort().is_bool() && !entailed && self.occurrs_entailed(node) {
            ctx.ast().ttrue()
        } else {
            // apply to children
            let kind = node.kind().clone();
            let children = node
                .children()
                .iter()
                .map(|child| self.apply_node(child, entailed, ctx))
                .collect();
            ctx.ast().create_node(kind, children)
        }
    }
}
