use indexmap::IndexSet;

use crate::{
    ast::{Node, NodeKind},
    context::Context,
};

use super::EquivalenceRule;

// TODO: Add the following rules
// - Absorption Or: A ∨ (A ∧ B) = A
// - Absorption And: A ∧ (A ∨ B) = A

/* AND */

/// Fold a conjunction of nodes:
/// -  (A /\ false) to false
/// -  (A /\ true) to A
///
/// Also returns false if the set of asserted nodes contains a false node.
#[derive(Debug, Clone, Copy)]
pub(super) struct AndConst;
impl EquivalenceRule for AndConst {
    fn apply(&self, node: &Node, asserted: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if asserted.contains(&ctx.ast().ffalse()) {
            return Some(ctx.ast().ffalse());
        }
        if *node.kind() == NodeKind::And {
            let mut new_children = Vec::with_capacity(node.children().len());
            for c in node.children() {
                if c.is_false() {
                    return Some(ctx.ast().ffalse());
                } else if c.is_true() {
                    continue;
                } else {
                    new_children.push(c.clone());
                }
            }
            if new_children.is_empty() {
                return Some(ctx.ast().ttrue());
            } else if new_children.len() < node.children().len() {
                return Some(ctx.ast().and(new_children));
            }
        }
        None
    }
}

/// Folds: (A /\ A) to A
#[derive(Debug, Clone, Copy)]
pub(super) struct AndIdem;
impl EquivalenceRule for AndIdem {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::And {
            let mut new_children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                new_children.insert(c.clone());
            }
            if new_children.is_empty() {
                return Some(ctx.ast().ttrue());
            } else if new_children.len() < node.children().len() {
                return Some(ctx.ast().and(new_children.into_iter().collect()));
            }
        }
        None
    }
}

/// Folds: (A /\ -A) to false
/// Also returns false if the set of asserted nodes contains a negated node.
#[derive(Debug, Clone, Copy)]
pub(super) struct AndComp;
impl EquivalenceRule for AndComp {
    fn apply(&self, node: &Node, asserted: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::And {
            let mut children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                let negated = match c.kind() {
                    NodeKind::Not => c.children().first().unwrap().clone(),
                    _ => ctx.ast().not(c.clone()),
                };
                if children.contains(&negated) || asserted.contains(&negated) {
                    return Some(ctx.ast().ffalse());
                }
                children.insert(c.clone());
            }
            None
        } else {
            None
        }
    }
}

/// Folds: (A /\ (A' /\ A'')) to (A /\ A' /\ A'')
#[derive(Debug, Clone, Copy)]
pub(super) struct AndAssocFlatten;
impl EquivalenceRule for AndAssocFlatten {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::And {
            let mut children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                if let NodeKind::And = c.kind() {
                    children.extend(c.children().iter().cloned());
                } else {
                    children.insert(c.clone());
                }
            }
            if children.len() > node.children().len() {
                return Some(ctx.ast().and(children.into_iter().collect()));
            }
        }
        None
    }
}

/* OR */

/// Fold a disjunction of nodes with constants:
/// -  (A \/ false) to A
/// -  (A \/ true) to true
#[derive(Debug, Clone, Copy)]
pub(super) struct OrConst;
impl EquivalenceRule for OrConst {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Or {
            let mut new_children = Vec::with_capacity(node.children().len());
            for c in node.children() {
                if c.is_true() {
                    return Some(ctx.ast().ttrue());
                } else if c.is_false() {
                    continue;
                } else {
                    new_children.push(c.clone());
                }
            }
            if new_children.is_empty() {
                return Some(ctx.ast().ffalse());
            } else if new_children.len() < node.children().len() {
                return Some(ctx.ast().or(new_children));
            }
        }
        None
    }
}

/// Folds: (A \/ A) to A
#[derive(Debug, Clone, Copy)]
pub(super) struct OrIdem;
impl EquivalenceRule for OrIdem {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Or {
            let mut new_children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                new_children.insert(c.clone());
            }
            if new_children.is_empty() {
                return Some(ctx.ast().ffalse());
            } else if new_children.len() < node.children().len() {
                return Some(ctx.ast().or(new_children.into_iter().collect()));
            }
        }
        None
    }
}

/// Folds: (A \/ -A) to true
#[derive(Debug, Clone, Copy)]
pub(super) struct OrComp;
impl EquivalenceRule for OrComp {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Or {
            let mut children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                let negated = match c.kind() {
                    NodeKind::Not => c.children().first().unwrap().clone(),
                    _ => ctx.ast().not(c.clone()),
                };
                if children.contains(&negated) {
                    return Some(ctx.ast().ttrue());
                }
                children.insert(c.clone());
            }
        }
        None
    }
}

/// Folds: (A \/ (A' \/ A'')) to (A \/ A' \/ A'')
#[derive(Debug, Clone, Copy)]
pub(super) struct OrAssocFlatten;
impl EquivalenceRule for OrAssocFlatten {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Or {
            let mut children = IndexSet::with_capacity(node.children().len());
            for c in node.children() {
                if let NodeKind::Or = c.kind() {
                    children.extend(c.children().iter().cloned());
                } else {
                    children.insert(c.clone());
                }
            }
            if children.len() > node.children().len() {
                return Some(ctx.ast().or(children.into_iter().collect()));
            }
        }
        None
    }
}

/* NOT */

/// Folds: -(-A) to A
#[derive(Debug, Clone, Copy)]
pub(super) struct NotDoubleNegation;
impl EquivalenceRule for NotDoubleNegation {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, _: &mut Context) -> Option<Node> {
        if let NodeKind::Not = node.kind() {
            debug_assert!(node.children().len() == 1);
            if let Some(child) = node.children().first() {
                if let NodeKind::Not = child.kind() {
                    debug_assert!(child.children().len() == 1);
                    return Some(child.children().first().unwrap().clone());
                }
            }
        }
        None
    }
}

/// Folds: -true to false and -false to true
#[derive(Debug, Clone, Copy)]
pub(super) struct NotConst;
impl EquivalenceRule for NotConst {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::Not = node.kind() {
            debug_assert!(node.children().len() == 1);
            let ch = node.children().first().unwrap();
            if ch.is_true() {
                return Some(ctx.ast().ffalse());
            } else if ch.is_false() {
                return Some(ctx.ast().ttrue());
            }
        }
        None
    }
}

/// Folds:
/// - A = A to true
/// - A = B to false if A != B and A and B are constants
#[derive(Debug, Clone, Copy)]
pub(super) struct EqualityTrivial;
impl EquivalenceRule for EqualityTrivial {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if let NodeKind::Eq = node.kind() {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if lhs == rhs {
                return Some(ctx.ast().ttrue());
            } else if lhs.is_const() && rhs.is_const() {
                return Some(ctx.ast().ffalse());
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {

    use crate::context::Sort;

    use super::*;

    #[test]
    fn test_and_idem() {
        let mut ctx = Context::default();

        let v = ctx.temp_var(Sort::Bool);
        let v = ctx.ast().variable(v);
        let vv = ctx.temp_var(Sort::Bool);
        let vv = ctx.ast().variable(vv);

        let conjuncts = vec![v.clone(), vv.clone(), v.clone()];
        let result = AndIdem.apply(&ctx.ast().and(conjuncts), &IndexSet::new(), &mut ctx);
        let expected = ctx.ast().and(vec![v.clone(), vv.clone()]);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_and_comp() {
        let mut ctx = Context::default();

        let v = ctx.temp_var(Sort::Bool);
        let v = ctx.ast().variable(v);
        let vv = ctx.temp_var(Sort::Bool);
        let vv = ctx.ast().variable(vv);

        let conjuncts = vec![v.clone(), ctx.ast().not(v.clone()), vv.clone()];
        let result = AndComp.apply(&ctx.ast().and(conjuncts), &IndexSet::new(), &mut ctx);

        assert_eq!(result, Some(ctx.ast().ffalse()));
    }

    #[test]
    fn test_or_idem() {
        let mut ctx = Context::default();

        let v = ctx.temp_var(Sort::Bool);
        let v = ctx.ast().variable(v);
        let vv = ctx.temp_var(Sort::Bool);
        let vv = ctx.ast().variable(vv);

        let conjuncts = vec![v.clone(), vv.clone(), v.clone()];
        let result = OrIdem.apply(&ctx.ast().or(conjuncts), &IndexSet::new(), &mut ctx);
        let expected = ctx.ast().or(vec![v.clone(), vv.clone()]);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_or_comp() {
        let mut ctx = Context::default();
        ctx.ast().set_optimize(false);

        let v = ctx.temp_var(Sort::Bool);
        let v = ctx.ast().variable(v);
        let vv = ctx.temp_var(Sort::Bool);
        let vv = ctx.ast().variable(vv);

        let disjuncts = vec![v.clone(), ctx.ast().not(v.clone()), vv.clone()];
        let disjuction = ctx.ast().or(disjuncts);
        let result = OrComp.apply(&disjuction, &IndexSet::new(), &mut ctx);

        assert_eq!(result, Some(ctx.ast().ttrue()));
    }

    #[test]
    fn test_not_double_negation() {
        let mut ctx = Context::default();

        let v = ctx.temp_var(Sort::Bool);
        let v = ctx.ast().variable(v);

        let not_v = ctx.ast().not(v.clone());

        // Calling ctx.ast().not again would directly return the child of the `Not` node, so we bypass the optimization in the Manager
        let not_not_v = ctx.ast().intern_node(NodeKind::Not, vec![not_v]);

        let result = NotDoubleNegation.apply(&not_not_v, &IndexSet::new(), &mut ctx);

        assert_eq!(result, Some(v));
    }

    #[test]
    fn test_not_true() {
        let mut ctx = Context::default();

        let t = ctx.ast().ttrue();
        let not_true = ctx.ast().intern_node(NodeKind::Not, vec![t]);
        let result = NotConst.apply(&not_true, &IndexSet::new(), &mut ctx);

        // Expect the result to be `false`
        assert_eq!(result, Some(ctx.ast().ffalse()));
    }

    #[test]
    fn test_not_false() {
        let mut ctx = Context::default();

        let f = ctx.ast().ffalse();
        let not_false = ctx.ast().intern_node(NodeKind::Not, vec![f]);
        let result = NotConst.apply(&not_false, &IndexSet::new(), &mut ctx);

        // Expect the result to be `true`
        assert_eq!(result, Some(ctx.ast().ttrue()));
    }
}
