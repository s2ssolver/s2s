use indexmap::IndexSet;

use crate::{
    ast::{Node, NodeKind},
    context::Sorted,
    interval::Interval,
    preprocess::simp::int::{normalize_ineq, LinearIntRealtion},
    Context,
};

use super::EquivalenceRule;

/// If on a path we already decided for a node to be true, then replaces this occurrens with true.
/// If we decided for the negatios of the node, replaces it with false instead.
#[derive(Debug, Clone, Copy)]
pub(super) struct PathPruning;

impl EquivalenceRule for PathPruning {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        decisions: &IndexSet<Node>,
        ctx: &mut Context,
    ) -> Option<Node> {
        if node.sort().is_bool() {
            if decisions.contains(node) {
                Some(ctx.ast().ttrue())
            } else if decisions.contains(&ctx.ast().not(node.clone())) {
                Some(ctx.ast().ffalse())
            } else {
                None
            }
        } else {
            None
        }
    }

    fn universal(&self) -> bool {
        false
    }
}

/// Compares a (linear) integer (in)equalities with an asserted fact.
/// If both have the same left-hand side, it checks if they are conflicting or if one implies the other.
/// If they are conflicting, it returns false.
/// If the fact implies the other, it returns true.
/// Otherwise, it returns None.
/// This is used to simplify integer (in)equalities in the forward rewriting.
#[derive(Debug, Clone, Copy)]
pub(super) struct LinIntForward;

impl LinIntForward {
    fn apply(fact: &Node, other: &Node, ctx: &mut Context) -> Option<Node> {
        let fact_norm = normalize_ineq(fact)?;
        let other_norm = normalize_ineq(other)?;
        // We check if they are

        // - conflicting: `fact` and `other` cannot be true at the same time. In that case, we return false.
        // - valid: `fact` implies `other`. In that case, we return true.
        // - otherwise, we return None.

        /// Compores two inequalities of the form:
        ///
        /// - `LHS op1 r1`
        /// - `LHS op2 r2`
        ///
        /// If they are conflicting, it returns false.
        /// If the the first implies the second, it returns true.
        /// Otherwise, it returns None.
        fn compare(fact: LinearIntRealtion, other: LinearIntRealtion) -> Option<bool> {
            fn to_interval(rel: &LinearIntRealtion) -> Vec<Interval> {
                let op = rel.op();
                let r = rel.rhs();
                let interval = match op {
                    NodeKind::Lt => Interval::bounded_above(r - 1),
                    NodeKind::Le => Interval::bounded_above(r),
                    NodeKind::Eq => Interval::new(r, r),
                    NodeKind::Ge => Interval::bounded_below(r),
                    NodeKind::Gt => Interval::bounded_below(r + 1),
                    _ => unreachable!(),
                };
                if rel.pol() {
                    vec![interval]
                } else {
                    // If the polarity is negative, we compute the complement of the interval [l, u]
                    // Left: (-inf, l-1]
                    // Right: [u+1, +inf)
                    let left = Interval::bounded_above(interval.lower() - 1.into());
                    let right = Interval::bounded_below(interval.upper() + 1.into());
                    vec![left, right]
                }
            }

            let fact_interval = to_interval(&fact);
            let other_interval = to_interval(&other);

            let mut disjoint = true;
            let mut subsumed = true;
            for left in fact_interval {
                for right in &other_interval {
                    // Check if the intervals are disjoint
                    disjoint &= left.intersect(*right).is_empty();
                    // Check if the fact is a subset of the other
                    subsumed &= left.is_subset(*right);
                }
            }
            debug_assert!(!disjoint || !subsumed);
            if disjoint {
                return Some(false);
            }
            if subsumed {
                return Some(true);
            }
            None
        }

        if fact_norm.lhs() == other_norm.lhs() {
            if compare(fact_norm, other_norm)? {
                return Some(ctx.ast().ttrue());
            } else {
                return Some(ctx.ast().ffalse());
            }
        }

        None
    }
}

impl EquivalenceRule for LinIntForward {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        decisions: &IndexSet<Node>,
        ctx: &mut Context,
    ) -> Option<Node> {
        match node.kind() {
            NodeKind::Lt
            | NodeKind::Le
            | NodeKind::Gt
            | NodeKind::Ge
            | NodeKind::Eq
            | NodeKind::Not => {
                for fact in decisions.iter() {
                    if let Some(equiv) = LinIntForward::apply(fact, node, ctx) {
                        return Some(equiv);
                    }
                }
            }
            _ => (),
        }

        None
    }

    fn universal(&self) -> bool {
        false
    }
}
