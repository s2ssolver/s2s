//! Rules that simplify the formula by replacing entailed literals with their values.

use indexmap::IndexSet;

use crate::node::{Node, NodeKind, NodeManager, Sorted, VarSubstitution};

use super::EntailmentRule;

/// Finds entailed boolean variables and replaces them with their values.
#[derive(Clone, Debug, Default)]
pub(super) struct EntailedBooleanVars;

impl EntailmentRule for EntailedBooleanVars {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        _pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution> {
        // This is only applicable if the node itself is asserted
        if !asserted.contains(node) {
            return None;
        }
        let mut subs = VarSubstitution::default();
        for a in asserted {
            if let NodeKind::Variable(v) = a.kind() {
                if v.sort().is_bool() {
                    if !subs.get(v).is_some() {
                        subs.add(v.clone(), mngr.ttrue());
                        return Some(subs);
                    }
                }
            } else if NodeKind::Not == *node.kind() {
                debug_assert!(node.children().len() == 1);
                let child = node.children().first().unwrap();
                if let NodeKind::Variable(v) = child.kind() {
                    if v.sort().is_bool() {
                        if !subs.get(v).is_some() {
                            subs.add(v.clone(), mngr.ffalse());
                            return Some(subs);
                        }
                    }
                }
            }
        }
        if subs.is_empty() {
            None
        } else {
            Some(subs)
        }
    }
}

/// Finds entailed equalities of the form `x = n` where `x` is a variable and `n` is a node.
/// Returns the substitution `x -> n`.
/// A rewrite pass will reduce the atom to `true` afterward.
#[derive(Clone, Debug, Default)]
pub(super) struct EntailedAssigments;

impl EntailmentRule for EntailedAssigments {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        _pol: bool,
        _: &mut NodeManager,
    ) -> Option<VarSubstitution> {
        // This is only applicable if the node itself is asserted
        if !asserted.contains(node) {
            return None;
        }
        if let NodeKind::Eq = *node.kind() {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if let NodeKind::Variable(v) = lhs.kind() {
                if rhs.size() < 10 || rhs.is_const() {
                    let mut subs = VarSubstitution::default();
                    subs.add(v.clone(), rhs.clone());
                    return Some(subs);
                }
            } else if let NodeKind::Variable(v) = rhs.kind() {
                if lhs.size() < 10 || lhs.is_const() {
                    let mut subs = VarSubstitution::default();
                    subs.add(v.clone(), lhs.clone());
                    return Some(subs);
                }
            }
        }
        None
    }
}
