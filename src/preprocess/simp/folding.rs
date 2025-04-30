use indexmap::IndexSet;

use crate::{ast::Node, Context};

use super::EquivalenceRule;

/// Folds Boolean constants
#[derive(Debug, Clone, Copy)]
pub struct FoldBoolConsts;
impl EquivalenceRule for FoldBoolConsts {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if node.as_bool_const()? {
            Some(ctx.ast().ttrue())
        } else {
            Some(ctx.ast().ffalse())
        }
    }
}

/// Fold. Integer constants.
#[derive(Debug, Clone, Copy)]
pub(super) struct FoldIntConsts;
impl EquivalenceRule for FoldIntConsts {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        let int = node.as_int_const()?;
        Some(ctx.ast().const_int(int))
    }
}

/// Folds string constants
#[derive(Debug, Clone, Copy)]
pub(super) struct FoldStringConsts;
impl EquivalenceRule for FoldStringConsts {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        let str = node.as_str_const()?;
        Some(ctx.ast().const_string(str))
    }
}
