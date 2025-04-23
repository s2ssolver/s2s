use super::*;
use crate::ast::{Node, NodeKind};

/// Rewrites `substr(w, s, l)` to `w[s:s+l]` if w is a constant strings and s and l are constant integers.
#[derive(Debug, Clone, Copy)]
pub(super) struct SubstrConst;
impl EquivalenceRule for SubstrConst {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::SubStr = node.kind() {
            let w = &node.children()[0];
            let s = &node.children()[1];
            let l = &node.children()[2];
            if let NodeKind::String(ref w) = w.kind() {
                if let NodeKind::Int(s) = s.kind() {
                    if let NodeKind::Int(l) = l.kind() {
                        let s = *s as usize;
                        let l = *l as usize;
                        let substr = w.drop(s).take(l);
                        return Some(ctx.ast().const_string(substr));
                    }
                }
            }
        }
        None
    }
}

/// Rewrites `at(w, s)` to `w[s]` if w is a constant strings and s is a constant integer.
/// If s is out of bounds, returns `""`.
#[derive(Debug, Clone, Copy)]
pub(super) struct AtConst;
impl EquivalenceRule for AtConst {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::At = node.kind() {
            let w = &node.children()[0];
            let s = &node.children()[1];
            if let NodeKind::String(ref w) = w.kind() {
                if let NodeKind::Int(s) = s.kind() {
                    let s = *s as usize;

                    match w.nth(s) {
                        Some(at) => return Some(ctx.ast().const_string(at.into())),
                        None => return Some(ctx.ast().empty_string()),
                    }
                }
            }
        }
        None
    }
}

/// Rewrites `substr(w, s, 0)` to `""` if s <= 0.
#[derive(Debug, Clone, Copy)]
pub(super) struct SubstrNegative;
impl EquivalenceRule for SubstrNegative {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::SubStr = node.kind() {
            let l = &node.children()[2];
            if let NodeKind::Int(l) = l.kind() {
                if *l <= 0 {
                    return Some(ctx.ast().empty_string());
                }
            }
        }
        None
    }
}

/// Rewrites `at(w, s)` to `""` if s < 0.
#[derive(Debug, Clone, Copy)]
pub(super) struct AtNegative;
impl EquivalenceRule for AtNegative {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::At = node.kind() {
            let s = &node.children()[1];
            if let NodeKind::Int(s) = s.kind() {
                if *s < 0 {
                    return Some(ctx.ast().empty_string());
                }
            }
        }
        None
    }
}
