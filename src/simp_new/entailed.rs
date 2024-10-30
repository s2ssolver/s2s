//! Rules that simplify the formula by replacing entailed literals with their values.

use crate::{
    context::Sorted,
    node::{Node, NodeKind, NodeManager, NodeSubstitution},
};

use super::{SimpRule, Simplification};

/// Finds entailed boolean variables and replaces them with their values.
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
pub struct RemoveEntailed;

impl SimpRule for RemoveEntailed {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            if node.is_literal() {
                let mut subs = NodeSubstitution::default();
                subs.add(node.clone(), mngr.ttrue(), mngr);
                // we need to add back the node, otherwise it will be removed completely
                return Some(Simplification::new(subs, Some(node.clone())));
            }
        }
        None
    }
}
