//! Rules that simplify the formula by replacing entailed literals with their values.

use crate::node::{Node, NodeKind, NodeManager, Sorted, VarSubstitution};

use super::{SimpRule, Simplification};

/// Finds entailed boolean variables and replaces them with their values.
#[derive(Clone, Default)]
pub struct EntailedBooleanVars;

impl SimpRule for EntailedBooleanVars {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            if let NodeKind::Variable(v) = node.kind() {
                if v.sort().is_bool() {
                    let mut subs = VarSubstitution::default();
                    subs.add(v.clone(), mngr.ttrue());
                    return Some(Simplification::new(subs, None));
                }
            } else if NodeKind::Not == *node.kind() {
                debug_assert!(node.children().len() == 1);
                let child = node.children().first().unwrap();
                if let NodeKind::Variable(v) = child.kind() {
                    if v.sort().is_bool() {
                        let mut subs = VarSubstitution::default();
                        subs.add(v.clone(), mngr.ffalse());
                        return Some(Simplification::new(subs, None));
                    }
                }
            }
        }
        None
    }

    fn name(&self) -> &str {
        "EntailedBooleanVars"
    }
}

/// Finds entailed equalities of the form `x = n` where `x` is a variable and `n` is a node.
/// Returns the substitution `x -> n`.
/// A rewrite pass will reduce the atom to `true` afterward.
#[derive(Clone, Default)]
pub struct EntailedAssigments;

impl SimpRule for EntailedAssigments {
    fn apply(&self, node: &Node, entailed: bool, _: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            if let NodeKind::Eq = *node.kind() {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if let NodeKind::Variable(v) = lhs.kind() {
                    if rhs.size() < 10 || rhs.is_const() {
                        let mut subs = VarSubstitution::default();
                        subs.add(v.clone(), rhs.clone());
                        return Some(Simplification::new(subs, None));
                    }
                } else if let NodeKind::Variable(v) = rhs.kind() {
                    if lhs.size() < 10 || lhs.is_const() {
                        let mut subs = VarSubstitution::default();
                        subs.add(v.clone(), lhs.clone());
                        return Some(Simplification::new(subs, None));
                    }
                }
            }
        }
        None
    }

    fn name(&self) -> &str {
        "EntailedAssigments"
    }
}
