use indexmap::IndexSet;

use crate::{
    interval::Interval,
    node::{Node, NodeKind, NodeManager},
};

use super::{int::normalize_ineq, EquivalenceRule};

/// Compares a node to the asserted nodes and simplifies the node if possible.
#[derive(Debug, Clone, Copy)]
pub(super) struct IntForwardReasoning;

impl IntForwardReasoning {
    fn apply(fact: &Node, other: &Node, mngr: &mut NodeManager) -> Option<Node> {
        let (lhs_fact, op_fact, rhs_fact) = normalize_ineq(fact)?;
        let (l2, op2, r2) = normalize_ineq(other)?;
        // We check if they are
        // - conflicting: `fact` and `other` cannot be true at the same time. In that case, we return false.
        // - valid: `fact` implies `other`. In that case, we return true.
        // - otherwise, we return None.

        /// Compores two inequalities of the form:
        /// - `LHS op1 r1`
        /// - `LHS op2 r2`
        /// If they are conflicting, it returns false.
        /// If the the first implies the second, it returns true.
        /// Otherwise, it returns None.
        fn compare(op_fact: &NodeKind, r_fact: i64, op2: &NodeKind, r2: i64) -> Option<bool> {
            fn to_interval(op: &NodeKind, r: i64) -> Interval {
                match op {
                    NodeKind::Lt => Interval::bounded_above(r - 1),
                    NodeKind::Le => Interval::bounded_above(r),
                    NodeKind::Eq => Interval::new(r, r),
                    NodeKind::Ge => Interval::bounded_below(r),
                    NodeKind::Gt => Interval::bounded_below(r + 1),
                    _ => unreachable!(),
                }
            }

            let left = to_interval(op_fact, r_fact);
            let right = to_interval(op2, r2);

            if left.intersect(right).is_empty() {
                Some(false)
            } else if left.is_subset(right) {
                // The asserted condition is more restrictive than the fact

                Some(true)
            } else {
                None
            }
        }

        if lhs_fact == l2 {
            if compare(&op_fact, rhs_fact, &op2, r2)? {
                return Some(mngr.ttrue());
            } else {
                return Some(mngr.ffalse());
            }
        }

        None
    }
}

impl EquivalenceRule for IntForwardReasoning {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        match node.kind() {
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge | NodeKind::Eq => {
                for fact in asserted.iter().filter(|a| *a != node) {
                    if let Some(equiv) = IntForwardReasoning::apply(fact, node, mngr) {
                        return Some(equiv);
                    }
                }
            }
            _ => (),
        }

        None
    }
}
