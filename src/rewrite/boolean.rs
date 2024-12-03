use crate::node::{self, Node, NodeKind, NodeManager};

use super::RewriteRule;

pub struct BoolConstFolding;

impl RewriteRule for BoolConstFolding {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            node::NodeKind::And => fold_and(node.children(), mngr),
            node::NodeKind::Or => fold_or(node.children(), mngr),
            node::NodeKind::Not => {
                debug_assert!(node.children().len() == 1);
                fold_not(node.children().first().unwrap(), mngr)
            }
            _ => None,
        }
    }
}

/// Fold a conjunction of nodes:
/// - If the conjunction contains a `false`, return `false`
/// - If the conjunction contains a `true`, remove it
/// - If there are no conjuncts left, return `true`
/// - If there is a single conjunct left, return that conjunct
fn fold_and(conjuncts: &[Node], mngr: &mut NodeManager) -> Option<Node> {
    let mut folded_conjuncts = Vec::with_capacity(conjuncts.len());

    for c in conjuncts {
        if c.is_false() {
            return Some(mngr.ffalse()); // Return `false` immediately
        } else if c.is_true() {
            continue; // Skip `true` values
        } else {
            folded_conjuncts.push(c.clone());
        }
    }

    match folded_conjuncts.len() {
        0 => Some(mngr.ttrue()),                    // All conjuncts were `true`
        1 => Some(folded_conjuncts.pop().unwrap()), // Single conjunct left
        _ if folded_conjuncts.len() == conjuncts.len() => None, // No changes
        _ => Some(mngr.and(folded_conjuncts)),      // Return the folded `and`
    }
}

/// Fold a disjunction of nodes:
/// - If the disjunction contains a `true`, return `true`
/// - If the disjunction contains a `false`, remove it
/// - If there are no disjuncts left, return `false`
/// - If there is a single disjunct left, return that disjunct
fn fold_or(disjuncts: &[Node], mngr: &mut NodeManager) -> Option<Node> {
    let mut folded_disjuncts = Vec::with_capacity(disjuncts.len());

    for d in disjuncts {
        if d.is_true() {
            return Some(mngr.ttrue()); // Return `true` immediately if any disjunct is `true`
        } else if d.is_false() {
            continue;
        } else {
            folded_disjuncts.push(d.clone());
        }
    }

    match folded_disjuncts.len() {
        0 => Some(mngr.ffalse()),                   // All disjuncts were `false`
        1 => Some(folded_disjuncts.pop().unwrap()), // Single disjunct left
        _ if folded_disjuncts.len() == disjuncts.len() => None, // No changes made
        _ => Some(mngr.or(folded_disjuncts)),       // Return the folded `or`
    }
}

/// Fold a negation of a node:
/// - If the node is `true`, return `false`
/// - If the node is `false`, return `true`
/// - If the node is a negation, return the child of the negation
fn fold_not(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if node.is_true() {
        Some(mngr.ffalse()) // Negation of `true` is `false`
    } else if node.is_false() {
        Some(mngr.ttrue()) // Negation of `false` is `true`
    } else if let NodeKind::Not = node.kind() {
        // Safely unwrap the child of the `Not` node
        if let Some(child) = node.children().first() {
            Some(child.clone()) // Double negation: ¬(¬a) becomes `a`
        } else {
            unreachable!("Formula is nod well-formed: Negation node without a child.");
        }
    } else {
        None // No folding performed
    }
}

#[cfg(test)]
mod tests {

    use node::Sort;

    use super::*;

    #[test]
    fn test_fold_and_all_true() {
        let mut mngr = NodeManager::default();

        // Case where all conjuncts are `true`
        let conjuncts = vec![mngr.ttrue(), mngr.ttrue(), mngr.ttrue()];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect the result to be `true`
        assert_eq!(result, Some(mngr.ttrue()));
    }

    #[test]
    fn test_fold_and_contains_false() {
        let mut mngr = NodeManager::default();

        // Case where the conjunction contains a `false`
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let conjuncts = vec![a.clone(), mngr.ffalse()];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect the result to be `false`
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_fold_and_contains_true() {
        let mut mngr = NodeManager::default();

        // Case where the conjunction contains a `true`, which should be removed
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let b = mngr.var(b);
        let conjuncts = vec![a.clone(), mngr.ttrue(), b.clone()];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect the result to be `a ∧ b` (without `true`)
        let expected = mngr.and(vec![a, b]);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_fold_and_single_conjunct_left() {
        let mut mngr = NodeManager::default();

        // Case where there is only one non-`true` conjunct left
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let conjuncts = vec![mngr.ttrue(), a.clone()];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect the result to be `a`
        assert_eq!(result, Some(a));
    }

    #[test]
    fn test_fold_and_no_changes() {
        let mut mngr = NodeManager::default();

        // Case where no folding occurs (no `true` or `false`)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let b = mngr.var(b);
        let conjuncts = vec![a.clone(), b.clone()];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect no changes, so `None` should be returned
        assert_eq!(result, None);
    }

    #[test]
    fn test_fold_and_empty_conjunction() {
        let mut mngr = NodeManager::default();

        // Case where the conjunction is empty
        let conjuncts: Vec<Node> = vec![];
        let result = fold_and(&conjuncts, &mut mngr);

        // Expect the result to be `true`
        assert_eq!(result, Some(mngr.ttrue()));
    }

    #[test]
    fn test_fold_or_all_false() {
        let mut mngr = NodeManager::default();

        // Case where all disjuncts are `false`
        let disjuncts = vec![mngr.ffalse(), mngr.ffalse(), mngr.ffalse()];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect the result to be `false`
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_fold_or_contains_true() {
        let mut mngr = NodeManager::default();

        // Case where the disjunction contains a `true`
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let disjuncts = vec![a.clone(), mngr.ttrue()];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect the result to be `true`
        assert_eq!(result, Some(mngr.ttrue()));
    }

    #[test]
    fn test_fold_or_contains_false() {
        let mut mngr = NodeManager::default();

        // Case where the disjunction contains a `false`, which should be removed
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let b = mngr.var(b);
        let disjuncts = vec![a.clone(), mngr.ffalse(), b.clone()];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect the result to be `a ∨ b` (without `false`)
        let expected = mngr.or(vec![a, b]);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_fold_or_single_disjunct_left() {
        let mut mngr = NodeManager::default();

        // Case where there is only one non-`false` disjunct left
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let disjuncts = vec![mngr.ffalse(), a.clone()];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect the result to be `a`
        assert_eq!(result, Some(a));
    }

    #[test]
    fn test_fold_or_no_changes() {
        let mut mngr = NodeManager::default();

        // Case where no folding occurs (no `true` or `false`)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let b = mngr.var(b);
        let disjuncts = vec![a.clone(), b.clone()];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect no changes, so `None` should be returned
        assert_eq!(result, None);
    }

    #[test]
    fn test_fold_or_empty_disjunction() {
        let mut mngr = NodeManager::default();

        // Case where the disjunction is empty
        let disjuncts: Vec<Node> = vec![];
        let result = fold_or(&disjuncts, &mut mngr);

        // Expect the result to be `false`
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_fold_not_true() {
        let mut mngr = NodeManager::default();

        // Negation of `true` should return `false`
        let node = mngr.ttrue();
        let result = fold_not(&node, &mut mngr);

        // Expect the result to be `false`
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_fold_not_false() {
        let mut mngr = NodeManager::default();

        // Negation of `false` should return `true`
        let node = mngr.ffalse();
        let result = fold_not(&node, &mut mngr);

        // Expect the result to be `true`
        assert_eq!(result, Some(mngr.ttrue()));
    }

    #[test]
    fn test_fold_not_double_negation() {
        let mut mngr = NodeManager::default();

        // Negation of a negation ¬(¬a) should return `a`
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let not_a = mngr.not(a.clone());
        let result = fold_not(&not_a, &mut mngr);

        // Expect the result to be `a` (double negation removed)
        assert_eq!(result, Some(a));
    }

    #[test]
    fn test_fold_not_no_folding() {
        let mut mngr = NodeManager::default();

        // Case where no folding occurs (e.g., `a`)
        let a = mngr.temp_var(Sort::Bool);
        let a = mngr.var(a);
        let result = fold_not(&a, &mut mngr);

        // Expect no folding, so `None` should be returned
        assert_eq!(result, None);
    }
}
