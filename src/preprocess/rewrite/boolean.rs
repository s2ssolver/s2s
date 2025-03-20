use indexmap::IndexSet;

use crate::node::{Node, NodeKind, NodeManager};

// TODO: Add the following rules
// - Absorption Or: A ∨ (A ∧ B) = A
// - Absorption And: A ∧ (A ∨ B) = A

/* AND */

/// Fold a conjunction of nodes:
/// -  (A /\ false) to false
/// -  (A /\ true) to A
pub fn and_const(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::And {
        let mut new_children = Vec::with_capacity(node.children().len());
        for c in node.children() {
            if c.is_false() {
                return Some(mngr.ffalse());
            } else if c.is_true() {
                continue;
            } else {
                new_children.push(c.clone());
            }
        }
        if new_children.is_empty() {
            return Some(mngr.ttrue());
        } else if new_children.len() < node.children().len() {
            return Some(mngr.and(new_children));
        }
    }
    None
}

/// Folds: (A /\ A) to A
pub fn and_idem(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::And {
        let mut new_children = IndexSet::with_capacity(node.children().len());
        for c in node.children() {
            new_children.insert(c.clone());
        }
        if new_children.is_empty() {
            return Some(mngr.ttrue());
        } else if new_children.len() < node.children().len() {
            return Some(mngr.and(new_children.into_iter().collect()));
        }
    }
    None
}

/// Folds: (A /\ -A) to false
pub fn and_comp(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::And {
        let mut children = IndexSet::with_capacity(node.children().len());
        for c in node.children() {
            if children.contains(&mngr.not(c.clone())) {
                return Some(mngr.ffalse());
            }
            children.insert(c.clone());
        }
        None
    } else {
        None
    }
}

/* OR */

/// Fold a disjunction of nodes with constants:
/// -  (A \/ false) to A
/// -  (A \/ true) to true
pub fn or_const(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Or {
        let mut new_children = Vec::with_capacity(node.children().len());
        for c in node.children() {
            if c.is_true() {
                return Some(mngr.ttrue());
            } else if c.is_false() {
                continue;
            } else {
                new_children.push(c.clone());
            }
        }
        if new_children.is_empty() {
            return Some(mngr.ffalse());
        } else if new_children.len() < node.children().len() {
            return Some(mngr.or(new_children));
        }
    }
    None
}

/// Folds: (A \/ A) to A
pub fn or_idem(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Or {
        let mut new_children = IndexSet::with_capacity(node.children().len());
        for c in node.children() {
            new_children.insert(c.clone());
        }
        if new_children.is_empty() {
            return Some(mngr.ffalse());
        } else if new_children.len() < node.children().len() {
            return Some(mngr.or(new_children.into_iter().collect()));
        }
    }
    None
}

/// Folds: (A \/ -A) to true
pub fn or_comp(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Or {
        let mut children = IndexSet::with_capacity(node.children().len());
        for c in node.children() {
            if children.contains(&mngr.not(c.clone())) {
                return Some(mngr.ttrue());
            }
            children.insert(c.clone());
        }
        None
    } else {
        None
    }
}

/* NOT */

/// Folds: -(-A) to A
pub fn not_double_negation(node: &Node) -> Option<Node> {
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

/// Folds: -true to false and -false to true
pub fn not_const(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::Not = node.kind() {
        debug_assert!(node.children().len() == 1);
        let ch = node.children().first().unwrap();
        if ch.is_true() {
            return Some(mngr.ffalse());
        } else if ch.is_false() {
            return Some(mngr.ttrue());
        }
    }
    None
}

/// Folds:
/// - A = A to true
/// - A = B to false if A != B and A and B are constants
pub fn equality_trivial(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::Eq = node.kind() {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        if lhs == rhs {
            Some(mngr.ttrue())
        } else {
            if lhs.is_const() && rhs.is_const() {
                Some(mngr.ffalse())
            } else {
                None
            }
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {

    use crate::node::Sort;

    use super::*;

    #[test]
    fn test_and_idem() {
        let mut mngr = NodeManager::default();

        let v = mngr.temp_var_node(Sort::Bool);
        let vv = mngr.temp_var_node(Sort::Bool);

        let conjuncts = vec![v.clone(), vv.clone(), v.clone()];
        let result = and_idem(&mngr.and(conjuncts), &mut mngr);
        let expected = mngr.and(vec![v.clone(), vv.clone()]);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_and_comp() {
        let mut mngr = NodeManager::default();

        let v = mngr.temp_var_node(Sort::Bool);
        let vv = mngr.temp_var_node(Sort::Bool);

        let conjuncts = vec![v.clone(), mngr.not(v.clone()), vv.clone()];
        let result = and_comp(&mngr.and(conjuncts), &mut mngr);

        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_or_idem() {
        let mut mngr = NodeManager::default();

        let v = mngr.temp_var_node(Sort::Bool);
        let vv = mngr.temp_var_node(Sort::Bool);

        let conjuncts = vec![v.clone(), vv.clone(), v.clone()];
        let result = or_idem(&mngr.or(conjuncts), &mut mngr);
        let expected = mngr.or(vec![v.clone(), vv.clone()]);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_or_comp() {
        let mut mngr = NodeManager::default();

        let v = mngr.temp_var_node(Sort::Bool);
        let vv = mngr.temp_var_node(Sort::Bool);

        let conjuncts = vec![v.clone(), mngr.not(v.clone()), vv.clone()];
        let result = or_comp(&mngr.or(conjuncts), &mut mngr);

        assert_eq!(result, Some(mngr.ttrue()));
    }

    #[test]
    fn test_not_double_negation() {
        let mut mngr = NodeManager::default();

        let v = mngr.temp_var_node(Sort::Bool);
        let not_v = mngr.not(v.clone());

        // Calling mngr.not again would directly return the child of the `Not` node, so we bypass the optimization in the Manager
        let not_not_v = mngr.intern_node(NodeKind::Not, vec![not_v]);

        let result = not_double_negation(&not_not_v);

        assert_eq!(result, Some(v));
    }

    #[test]
    fn test_not_true() {
        let mut mngr = NodeManager::default();

        let t = mngr.ttrue();
        let not_true = mngr.intern_node(NodeKind::Not, vec![t]);
        let result = not_const(&not_true, &mut mngr);

        // Expect the result to be `false`
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_not_false() {
        let mut mngr = NodeManager::default();

        let f = mngr.ffalse();
        let not_false = mngr.intern_node(NodeKind::Not, vec![f]);
        let result = not_const(&not_false, &mut mngr);

        // Expect the result to be `true`
        assert_eq!(result, Some(mngr.ttrue()));
    }
}
