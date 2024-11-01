//! Rules that simplify the formula by replacing entailed literals with their values.

use indexmap::IndexSet;

use crate::{
    context::Sorted,
    node::{Node, NodeKind, NodeManager, NodeSubstitution},
};

use super::{SimpRule, Simplification};

/// Finds entailed boolean variables and replaces them with their values.
#[derive(Clone, Default)]
pub struct EntailedBooleanVars;

impl SimpRule for EntailedBooleanVars {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            if let NodeKind::Variable(v) = node.kind() {
                if v.sort().is_bool() {
                    let mut subs = NodeSubstitution::default();
                    subs.add(node.clone(), mngr.ttrue(), mngr);
                    return Some(Simplification::new(subs, None));
                }
            } else if NodeKind::Not == *node.kind() {
                debug_assert!(node.children().len() == 1);
                let child = node.children().first().unwrap();
                if let NodeKind::Variable(v) = child.kind() {
                    if v.sort().is_bool() {
                        let mut subs = NodeSubstitution::default();
                        subs.add(child.clone(), mngr.ffalse(), mngr);
                        return Some(Simplification::new(subs, None));
                    }
                }
            }
        }
        None
    }
}

/// Finds entailed equalities of the form `x = n` where `x` is a variable and `n` is a node.
/// Returns the substitution `x -> n`.
/// A rewrite pass will reduce the atom to `true` afterward.
#[derive(Clone, Default)]
pub struct EntailedAssigments;

impl SimpRule for EntailedAssigments {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            if let NodeKind::Eq = *node.kind() {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if let NodeKind::Variable(_) = lhs.kind() {
                    let mut subs = NodeSubstitution::default();
                    subs.add(lhs.clone(), rhs.clone(), mngr);
                    return Some(Simplification::new(subs, None));
                } else if let NodeKind::Variable(_) = rhs.kind() {
                    let mut subs = NodeSubstitution::default();
                    subs.add(rhs.clone(), lhs.clone(), mngr);
                    return Some(Simplification::new(subs, None));
                }
            }
        }
        None
    }
}

/// Removes all other occurrences of entailed literals from the formula by replacing them with `true` or `false`.
#[derive(Clone, Default)]
pub struct RemoveEntailed {
    // All nodes that have a non-entailed occurrence.
    non_entailed: IndexSet<Node>,
}

impl RemoveEntailed {
    fn occurs_non_entailed(&self, node: &Node) -> bool {
        self.non_entailed.contains(node)
    }

    fn update_non_entailed(&mut self, node: &Node, entailed: bool) {
        if !node.sort().is_bool() {
            return;
        }

        if !entailed {
            self.non_entailed.insert(node.clone());
        }

        let entailed = entailed && *node.kind() == NodeKind::And;
        for child in node.children() {
            self.update_non_entailed(child, entailed);
        }
    }
}

impl SimpRule for RemoveEntailed {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed && node.sort().is_bool() && self.occurs_non_entailed(node) {
            let mut subs = NodeSubstitution::default();
            subs.add(node.clone(), mngr.ttrue(), mngr);
            // we need to add back the node, otherwise it will be removed completely
            return Some(Simplification::new(subs, Some(node.clone())));
        }
        None
    }

    fn init(&mut self, root: &Node) {
        self.update_non_entailed(root, true);
    }
}
