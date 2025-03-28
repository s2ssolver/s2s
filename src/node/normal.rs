use super::{Node, NodeKind, NodeManager};

/// Converts a node to *Boolean Normal Form* (BNF).
/// A node is in BNF if the only Boolean connectives are `or`, `and`, and `not`.
pub fn to_bnf(node: &Node, mngr: &mut NodeManager) -> Node {
    match node.kind() {
        NodeKind::Or | NodeKind::And => {
            let children_in_bnf: Vec<Node> = node
                .children()
                .iter()
                .map(|child| to_bnf(child, mngr))
                .collect();

            match node.kind() {
                NodeKind::Or => mngr.or(children_in_bnf),
                NodeKind::And => mngr.and(children_in_bnf),
                _ => unreachable!(), // This match arm handles only Or and And
            }
        }
        NodeKind::Imp => {
            // Implication: a -> b is transformed into ¬a ∨ b
            let children = node.children();
            let left_bnf = to_bnf(&children[0], mngr);
            let right_bnf = to_bnf(&children[1], mngr);
            let left_not = mngr.not(left_bnf);

            mngr.or(vec![left_not, right_bnf])
        }
        NodeKind::Equiv => {
            // Equivalence: a <-> b is transformed into (a -> b) ∧ (b -> a)
            let children = node.children();
            let left = children[0].clone();
            let right = children[1].clone();

            let left_to_right = mngr.imp(left.clone(), right.clone());
            let right_to_left = mngr.imp(right, left);
            let biimp = mngr.and(vec![left_to_right, right_to_left]);

            to_bnf(&biimp, mngr)
        }
        NodeKind::Not => {
            // Negation: ¬a is transformed by recursively applying BNF to `a`
            let child_bnf = to_bnf(&node.children()[0], mngr);
            mngr.not(child_bnf)
        }
        _ => {
            // Base case: if the node is not a Boolean connective, return it unchanged
            node.clone()
        }
    }
}

/// Converts a node to *Negation Normal Form* (NNF).
/// A node is in NNF if it is in BNF and negations only occur in front of predicates.
/// If the node is not in BNF, it is first converted to BNF.
pub fn to_nnf(node: &Node, mngr: &mut NodeManager) -> Node {
    match node.kind() {
        NodeKind::Or | NodeKind::And => {
            let children_in_nnf: Vec<Node> = node
                .children()
                .iter()
                .map(|child| to_nnf(child, mngr))
                .collect();

            match node.kind() {
                NodeKind::Or => mngr.or(children_in_nnf),
                NodeKind::And => mngr.and(children_in_nnf),
                _ => unreachable!(), // This match arm handles only Or and And
            }
        }
        NodeKind::Not => {
            debug_assert_eq!(node.children().len(), 1);
            let child = &node.children()[0];
            match child.kind() {
                NodeKind::Not => {
                    // Double negation: ¬¬a is equivalent to a
                    debug_assert_eq!(child.children().len(), 1);
                    to_nnf(&child.children()[0], mngr)
                }
                NodeKind::And | NodeKind::Or => {
                    // De Morgan's laws: ¬(a ∧ b) is equivalent to ¬a ∨ ¬b
                    let mut nnf_children = Vec::with_capacity(child.children().len());
                    for ch in child.children() {
                        let negated_child = mngr.not(ch.clone());
                        nnf_children.push(to_nnf(&negated_child, mngr));
                    }
                    match child.kind() {
                        NodeKind::Or => mngr.and(nnf_children),
                        NodeKind::And => mngr.or(nnf_children),
                        _ => unreachable!(), // This match arm handles only Or and And
                    }
                }
                NodeKind::Imp | NodeKind::Equiv => {
                    // Convert to BNF first
                    let bnf_node = to_bnf(child, mngr);
                    let not_bnf_node = mngr.not(bnf_node);
                    to_nnf(&not_bnf_node, mngr)
                }
                _ => node.clone(), // must be a literal, keep it as is
            }
        }
        NodeKind::Imp | NodeKind::Equiv => {
            // convert to BNF first
            let bnf_node = to_bnf(node, mngr);
            to_nnf(&bnf_node, mngr)
        }

        _ => node.clone(),
    }
}

#[cfg(test)]
mod tests {

    use crate::node::Sort;

    use super::*;

    #[test]
    fn test_to_bnf_simple_or() {
        let mut mngr = NodeManager::default();

        let va = mngr.temp_var(Sort::Bool);
        let vb = mngr.temp_var(Sort::Bool);

        // a ∨ b should remain unchanged in BNF
        let a = mngr.var(va);
        let b = mngr.var(vb);
        let or_node = mngr.or(vec![a.clone(), b.clone()]);

        let result = to_bnf(&or_node, &mut mngr);
        assert_eq!(result, or_node);
    }

    #[test]
    fn test_to_bnf_simple_and() {
        let mut mngr = NodeManager::default();

        let va = mngr.temp_var(Sort::Bool);
        let vb = mngr.temp_var(Sort::Bool);

        // a ∧ b should remain unchanged in BNF
        let a = mngr.var(va);
        let b = mngr.var(vb);
        let and_node = mngr.and(vec![a.clone(), b.clone()]);

        let result = to_bnf(&and_node, &mut mngr);
        assert_eq!(result, and_node);
    }

    #[test]
    fn test_to_bnf_implication() {
        let mut mngr = NodeManager::default();

        let va = mngr.temp_var(Sort::Bool);
        let vb = mngr.temp_var(Sort::Bool);

        // a -> b should be converted to ¬a ∨ b
        let a = mngr.var(va);
        let b = mngr.var(vb);
        let imp_node = mngr.imp(a.clone(), b.clone());

        let result = to_bnf(&imp_node, &mut mngr);

        // The expected result is ¬a ∨ b
        let nota = mngr.not(a);
        let expected = mngr.or(vec![nota, b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_bnf_equiv() {
        let mut mngr = NodeManager::default();

        let va = mngr.temp_var(Sort::Bool);
        let vb = mngr.temp_var(Sort::Bool);

        // a <-> b should be converted to (a -> b) ∧ (b -> a)
        // and then converted to (¬a ∨ b) ∧ (¬b ∨ a)
        let a = mngr.var(va);
        let b = mngr.var(vb);
        let equiv_node = mngr.equiv(a.clone(), b.clone());

        let result = to_bnf(&equiv_node, &mut mngr);

        // The expected result is (a -> b) ∧ (b -> a)
        let nota = mngr.not(a.clone());
        let notb = mngr.not(b.clone());

        let left_to_right = mngr.or(vec![nota.clone(), b.clone()]);
        let right_to_left = mngr.or(vec![notb, a]);
        let expected = mngr.and(vec![left_to_right, right_to_left]);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_bnf_nested() {
        let mut mngr = NodeManager::default();
        mngr.set_optimize(false);

        let va = mngr.temp_var(Sort::Bool);
        let vb = mngr.temp_var(Sort::Bool);

        // ¬(a -> b) should convert to ¬(¬a ∨ b), then simplify
        let a = mngr.var(va);
        let b = mngr.var(vb);
        let imp_node = mngr.imp(a.clone(), b.clone());
        let not_imp_node = mngr.not(imp_node);

        let result = to_bnf(&not_imp_node, &mut mngr);

        // The expected result is ¬(¬a ∨ b)
        let left_not = mngr.not(a);
        let or_node = mngr.or(vec![left_not, b]);
        let expected = mngr.not(or_node);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_simple_or() {
        let mut mngr = NodeManager::default();

        // a ∨ b should remain unchanged in NNF
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let or_node = mngr.or(vec![var_a, var_b]);

        let result = to_nnf(&or_node, &mut mngr);
        assert_eq!(result, or_node);
    }

    #[test]
    fn test_to_nnf_simple_and() {
        let mut mngr = NodeManager::default();

        // a ∧ b should remain unchanged in NNF
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let and_node = mngr.and(vec![var_a, var_b]);

        let result = to_nnf(&and_node, &mut mngr);
        assert_eq!(result, and_node);
    }

    #[test]
    fn test_to_nnf_double_negation() {
        let mut mngr = NodeManager::default();

        // ¬¬a should simplify to a
        let a = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let negated_a = mngr.not(var_a.clone());
        let double_not_node = mngr.not(negated_a);

        let result = to_nnf(&double_not_node, &mut mngr);

        assert_eq!(result, var_a);
    }

    #[test]
    fn test_to_nnf_de_morgans_law_or() {
        let mut mngr = NodeManager::default();

        // ¬(a ∨ b) should transform to ¬a ∧ ¬b (De Morgan's law)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let or_node = mngr.or(vec![var_a.clone(), var_b.clone()]);
        let not_or_node = mngr.not(or_node);

        let not_a = mngr.not(var_a);
        let not_b = mngr.not(var_b);
        let result = to_nnf(&not_or_node, &mut mngr);

        let expected = mngr.and(vec![not_a, not_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_de_morgans_law_and() {
        let mut mngr = NodeManager::default();

        // ¬(a ∧ b) should transform to ¬a ∨ ¬b (De Morgan's law)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let and_node = mngr.and(vec![var_a.clone(), var_b.clone()]);
        let not_and_node = mngr.not(and_node);

        let not_a = mngr.not(var_a);
        let not_b = mngr.not(var_b);
        let result = to_nnf(&not_and_node, &mut mngr);

        let expected = mngr.or(vec![not_a, not_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_implication() {
        let mut mngr = NodeManager::default();

        // a -> b should convert to ¬a ∨ b in NNF
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let imp_node = mngr.imp(var_a.clone(), var_b.clone());

        let result = to_nnf(&imp_node, &mut mngr);

        let not_a = mngr.not(var_a);
        let expected = mngr.or(vec![not_a, var_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_equivalence() {
        let mut mngr = NodeManager::default();

        // a <-> b should convert to (¬a ∨ b) ∧ (¬b ∨ a) in NNF
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let equiv_node = mngr.equiv(var_a.clone(), var_b.clone());

        let result = to_nnf(&equiv_node, &mut mngr);

        let not_a = mngr.not(var_a.clone());
        let not_b = mngr.not(var_b.clone());
        let left = mngr.or(vec![not_a, var_b]);
        let right = mngr.or(vec![not_b, var_a]);
        let expected = mngr.and(vec![left, right]);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_not_equivalence() {
        let mut mngr = NodeManager::default();

        // not(a <-> b) should convert to
        // <==> not((¬a ∨ b) ∧ (¬b ∨ a))
        // <==> not(¬a ∨ b) ∨ not(¬b ∨ a)
        // <==> (a ∧ ¬b) ∨ (b ∧ ¬a)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let var_a = mngr.var(a.clone());
        let var_b = mngr.var(b.clone());
        let equiv_node = mngr.equiv(var_a.clone(), var_b.clone());
        let not_equiv_node = mngr.not(equiv_node);

        let result = to_nnf(&not_equiv_node, &mut mngr);

        let a = mngr.var(a);
        let b = mngr.var(b);
        let not_b = mngr.not(b.clone());
        let not_a = mngr.not(a.clone());
        let left = mngr.and(vec![a, not_b]);
        let right = mngr.and(vec![b, not_a]);
        let expected = mngr.or(vec![left, right]);

        assert_eq!(
            result, expected,
            "\nExpected: {}\nGot: {}",
            expected, result
        );
    }

    #[test]
    fn test_nnf_nested() {
        let mut mngr = NodeManager::default();

        // not(a /\ not(b \/ c)) should convert to not(a) \/ (b /\ c)
        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let c = mngr.temp_var(Sort::Bool);

        let var_a = mngr.var(a);
        let var_b = mngr.var(b);
        let var_c = mngr.var(c);

        let b_or_c = mngr.or(vec![var_b.clone(), var_c.clone()]);
        let not_b_or_c = mngr.not(b_or_c);
        let a_and_not_b_or_c = mngr.and(vec![var_a.clone(), not_b_or_c]);
        let not_a_and_b_and_c = mngr.not(a_and_not_b_or_c);

        // expected result is not(a) \/ (b /\ c)
        let not_a = mngr.not(var_a);
        let b_and_c = mngr.or(vec![var_b, var_c]);
        let expected = mngr.or(vec![not_a, b_and_c]);

        let result = to_nnf(&not_a_and_b_and_c, &mut mngr);

        assert_eq!(
            result, expected,
            "\nExpected: {}\nGot: {}",
            expected, result
        );
    }
}
