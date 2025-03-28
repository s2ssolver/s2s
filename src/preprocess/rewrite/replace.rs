use super::*;
use crate::node::{Node, NodeKind, NodeManager};

/// Idempency of replacement operation.
/// - `replace(x, y, y) = x`
/// - `replace_all(x, y, y) = x`
#[derive(Debug, Clone, Copy)]
pub(super) struct ReplaceIdem;
impl EquivalenceRule for ReplaceIdem {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, _: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            NodeKind::Replace | NodeKind::ReplaceAll => {
                debug_assert_eq!(node.children().len(), 3);
                let from = node.children()[1].clone();
                let to = node.children()[2].clone();
                if from == to {
                    return Some(node.children()[0].clone());
                }
            }
            _ => {}
        }
        None
    }
}

/// Replacement operation on the empty string.
/// - `replace(_all)("", "", z) = z`
/// - `replace(_all)("", y, z) = ""` if y is a constant string with y != ""
#[derive(Debug, Clone, Copy)]
pub(super) struct ReplaceInEpsilon;
impl EquivalenceRule for ReplaceInEpsilon {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            NodeKind::Replace | NodeKind::ReplaceAll => {
                debug_assert_eq!(node.children().len(), 3);
                let in_ = node.children()[0].clone();
                let from = node.children()[1].clone();
                let to = node.children()[2].clone();
                if let NodeKind::String(x) = in_.kind() {
                    if x.is_empty() {
                        if let NodeKind::String(y) = from.kind() {
                            if y.is_empty() {
                                return Some(to);
                            } else {
                                return Some(mngr.empty_string());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }
}

/// Replacement operation on the same string.
/// - `replace(x, x, y) = y`
/// - `replace_all(x, x, y) = y`
#[derive(Debug, Clone, Copy)]
pub(super) struct ReplaceSelf;
impl EquivalenceRule for ReplaceSelf {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, _: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            NodeKind::Replace | NodeKind::ReplaceAll => {
                debug_assert_eq!(node.children().len(), 3);
                let in_ = node.children()[0].clone();
                let from = node.children()[1].clone();
                let to = node.children()[2].clone();
                if in_ == from {
                    return Some(to);
                }
            }
            _ => {}
        }
        None
    }
}

/// Replacement operation on the empty string.
/// - `replace(x, "", y)` -> y.x
/// - `replace_all(x, "", y)` -> x
#[derive(Debug, Clone, Copy)]
pub(super) struct ReplaceEpsilon;
impl EquivalenceRule for ReplaceEpsilon {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            NodeKind::Replace | NodeKind::ReplaceAll => {
                debug_assert_eq!(node.children().len(), 3);
                let in_ = node.children()[0].clone();
                let from = node.children()[1].clone();
                let to = node.children()[2].clone();
                if let NodeKind::String(x) = from.kind() {
                    if x.is_empty() {
                        match node.kind() {
                            NodeKind::ReplaceAll => {
                                return Some(in_);
                            }
                            NodeKind::Replace => {
                                return Some(mngr.concat(vec![to, in_]));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }
}
