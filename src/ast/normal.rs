use crate::context::Context;

use super::{Node, NodeKind};

/// Converts a node to *Boolean Normal Form* (BNF).
/// A node is in BNF if the only Boolean connectives are `or`, `and`, and `not`.
pub fn to_bnf(node: &Node, ctx: &mut Context) -> Node {
    match node.kind() {
        NodeKind::Or | NodeKind::And => {
            let children_in_bnf: Vec<Node> = node
                .children()
                .iter()
                .map(|child| to_bnf(child, ctx))
                .collect();

            match node.kind() {
                NodeKind::Or => ctx.ast().or(children_in_bnf),
                NodeKind::And => ctx.ast().and(children_in_bnf),
                _ => unreachable!(), // This match arm handles only Or and And
            }
        }
        NodeKind::Imp => {
            // Implication: a -> b is transformed into ¬a ∨ b
            let children = node.children();
            let left_bnf = to_bnf(&children[0], ctx);
            let right_bnf = to_bnf(&children[1], ctx);
            let left_not = ctx.ast().not(left_bnf);
            ctx.ast().or(vec![left_not, right_bnf])
        }
        NodeKind::Equiv => {
            // Equivalence: a <-> b is transformed into (a -> b) ∧ (b -> a)
            let children = node.children();
            let left = children[0].clone();
            let right = children[1].clone();

            let left_to_right = ctx.ast().imp(left.clone(), right.clone());
            let right_to_left = ctx.ast().imp(right, left);
            let biimp = ctx.ast().and(vec![left_to_right, right_to_left]);

            to_bnf(&biimp, ctx)
        }
        NodeKind::Not => {
            // Negation: ¬a is transformed by recursively applying BNF to `a`
            let child_bnf = to_bnf(&node.children()[0], ctx);
            ctx.ast().not(child_bnf)
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
pub fn to_nnf(node: &Node, ctx: &mut Context) -> Node {
    match node.kind() {
        NodeKind::Or | NodeKind::And => {
            let children_in_nnf: Vec<Node> = node
                .children()
                .iter()
                .map(|child| to_nnf(child, ctx))
                .collect();

            match node.kind() {
                NodeKind::Or => ctx.ast().or(children_in_nnf),
                NodeKind::And => ctx.ast().and(children_in_nnf),
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
                    to_nnf(&child.children()[0], ctx)
                }
                NodeKind::And | NodeKind::Or => {
                    // De Morgan's laws: ¬(a ∧ b) is equivalent to ¬a ∨ ¬b
                    let mut nnf_children = Vec::with_capacity(child.children().len());
                    for ch in child.children() {
                        let negated_child = ctx.ast().not(ch.clone());
                        nnf_children.push(to_nnf(&negated_child, ctx));
                    }
                    match child.kind() {
                        NodeKind::Or => ctx.ast().and(nnf_children),
                        NodeKind::And => ctx.ast().or(nnf_children),
                        _ => unreachable!(), // This match arm handles only Or and And
                    }
                }
                NodeKind::Imp | NodeKind::Equiv => {
                    // Convert to BNF first
                    let bnf_node = to_bnf(child, ctx);
                    let not_bnf_node = ctx.ast().not(bnf_node);
                    to_nnf(&not_bnf_node, ctx)
                }
                _ => node.clone(), // must be a literal, keep it as is
            }
        }
        NodeKind::Imp | NodeKind::Equiv => {
            // convert to BNF first
            let bnf_node = to_bnf(node, ctx);
            to_nnf(&bnf_node, ctx)
        }

        _ => node.clone(),
    }
}

#[cfg(test)]
mod tests {

    use crate::context::Sort;

    use super::*;

    #[test]
    fn test_to_bnf_simple_or() {
        let mut ctx = Context::default();

        let va = ctx.temp_var(Sort::Bool);
        let vb = ctx.temp_var(Sort::Bool);

        // a ∨ b should remain unchanged in BNF
        let a = ctx.ast().variable(va);
        let b = ctx.ast().variable(vb);
        let or_node = ctx.ast().or(vec![a.clone(), b.clone()]);

        let result = to_bnf(&or_node, &mut ctx);
        assert_eq!(result, or_node);
    }

    #[test]
    fn test_to_bnf_simple_and() {
        let mut ctx = Context::default();

        let va = ctx.temp_var(Sort::Bool);
        let vb = ctx.temp_var(Sort::Bool);

        // a ∧ b should remain unchanged in BNF
        let a = ctx.ast().variable(va);
        let b = ctx.ast().variable(vb);
        let and_node = ctx.ast().and(vec![a.clone(), b.clone()]);

        let result = to_bnf(&and_node, &mut ctx);
        assert_eq!(result, and_node);
    }

    #[test]
    fn test_to_bnf_implication() {
        let mut ctx = Context::default();

        let va = ctx.temp_var(Sort::Bool);
        let vb = ctx.temp_var(Sort::Bool);

        // a -> b should be converted to ¬a ∨ b
        let a = ctx.ast().variable(va);
        let b = ctx.ast().variable(vb);
        let imp_node = ctx.ast().imp(a.clone(), b.clone());

        let result = to_bnf(&imp_node, &mut ctx);

        // The expected result is ¬a ∨ b
        let nota = ctx.ast().not(a);
        let expected = ctx.ast().or(vec![nota, b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_bnf_equiv() {
        let mut ctx = Context::default();

        let va = ctx.temp_var(Sort::Bool);
        let vb = ctx.temp_var(Sort::Bool);

        // a <-> b should be converted to (a -> b) ∧ (b -> a)
        // and then converted to (¬a ∨ b) ∧ (¬b ∨ a)
        let a = ctx.ast().variable(va);
        let b = ctx.ast().variable(vb);
        let equiv_node = ctx.ast().equiv(a.clone(), b.clone());

        let result = to_bnf(&equiv_node, &mut ctx);

        // The expected result is (a -> b) ∧ (b -> a)
        let nota = ctx.ast().not(a.clone());
        let notb = ctx.ast().not(b.clone());

        let left_to_right = ctx.ast().or(vec![nota.clone(), b.clone()]);
        let right_to_left = ctx.ast().or(vec![notb, a]);
        let expected = ctx.ast().and(vec![left_to_right, right_to_left]);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_bnf_nested() {
        let mut ctx = Context::default();
        ctx.ast().set_simplify(false);

        let va = ctx.temp_var(Sort::Bool);
        let vb = ctx.temp_var(Sort::Bool);

        // ¬(a -> b) should convert to ¬(¬a ∨ b), then simplify
        let a = ctx.ast().variable(va);
        let b = ctx.ast().variable(vb);
        let imp_node = ctx.ast().imp(a.clone(), b.clone());
        let not_imp_node = ctx.ast().not(imp_node);

        let result = to_bnf(&not_imp_node, &mut ctx);

        // The expected result is ¬(¬a ∨ b)
        let left_not = ctx.ast().not(a);
        let or_node = ctx.ast().or(vec![left_not, b]);
        let expected = ctx.ast().not(or_node);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_simple_or() {
        let mut ctx = Context::default();

        // a ∨ b should remain unchanged in NNF
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let or_node = ctx.ast().or(vec![var_a, var_b]);

        let result = to_nnf(&or_node, &mut ctx);
        assert_eq!(result, or_node);
    }

    #[test]
    fn test_to_nnf_simple_and() {
        let mut ctx = Context::default();

        // a ∧ b should remain unchanged in NNF
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let and_node = ctx.ast().and(vec![var_a, var_b]);

        let result = to_nnf(&and_node, &mut ctx);
        assert_eq!(result, and_node);
    }

    #[test]
    fn test_to_nnf_double_negation() {
        let mut ctx = Context::default();

        // ¬¬a should simplify to a
        let a = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let negated_a = ctx.ast().not(var_a.clone());
        let double_not_node = ctx.ast().not(negated_a);

        let result = to_nnf(&double_not_node, &mut ctx);

        assert_eq!(result, var_a);
    }

    #[test]
    fn test_to_nnf_de_morgans_law_or() {
        let mut ctx = Context::default();

        // ¬(a ∨ b) should transform to ¬a ∧ ¬b (De Morgan's law)
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let or_node = ctx.ast().or(vec![var_a.clone(), var_b.clone()]);
        let not_or_node = ctx.ast().not(or_node);

        let not_a = ctx.ast().not(var_a);
        let not_b = ctx.ast().not(var_b);
        let result = to_nnf(&not_or_node, &mut ctx);

        let expected = ctx.ast().and(vec![not_a, not_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_de_morgans_law_and() {
        let mut ctx = Context::default();

        // ¬(a ∧ b) should transform to ¬a ∨ ¬b (De Morgan's law)
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let and_node = ctx.ast().and(vec![var_a.clone(), var_b.clone()]);
        let not_and_node = ctx.ast().not(and_node);

        let not_a = ctx.ast().not(var_a);
        let not_b = ctx.ast().not(var_b);
        let result = to_nnf(&not_and_node, &mut ctx);

        let expected = ctx.ast().or(vec![not_a, not_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_implication() {
        let mut ctx = Context::default();

        // a -> b should convert to ¬a ∨ b in NNF
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let imp_node = ctx.ast().imp(var_a.clone(), var_b.clone());

        let result = to_nnf(&imp_node, &mut ctx);

        let not_a = ctx.ast().not(var_a);
        let expected = ctx.ast().or(vec![not_a, var_b]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_equivalence() {
        let mut ctx = Context::default();

        // a <-> b should convert to (¬a ∨ b) ∧ (¬b ∨ a) in NNF
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let equiv_node = ctx.ast().equiv(var_a.clone(), var_b.clone());

        let result = to_nnf(&equiv_node, &mut ctx);

        let not_a = ctx.ast().not(var_a.clone());
        let not_b = ctx.ast().not(var_b.clone());
        let left = ctx.ast().or(vec![not_a, var_b]);
        let right = ctx.ast().or(vec![not_b, var_a]);
        let expected = ctx.ast().and(vec![left, right]);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_nnf_not_equivalence() {
        let mut ctx = Context::default();

        // not(a <-> b) should convert to
        // <==> not((¬a ∨ b) ∧ (¬b ∨ a))
        // <==> not(¬a ∨ b) ∨ not(¬b ∨ a)
        // <==> (a ∧ ¬b) ∨ (b ∧ ¬a)
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let var_a = ctx.ast().variable(a.clone());
        let var_b = ctx.ast().variable(b.clone());
        let equiv_node = ctx.ast().equiv(var_a.clone(), var_b.clone());
        let not_equiv_node = ctx.ast().not(equiv_node);

        let result = to_nnf(&not_equiv_node, &mut ctx);

        let a = ctx.ast().variable(a);
        let b = ctx.ast().variable(b);
        let not_b = ctx.ast().not(b.clone());
        let not_a = ctx.ast().not(a.clone());
        let left = ctx.ast().and(vec![a, not_b]);
        let right = ctx.ast().and(vec![b, not_a]);
        let expected = ctx.ast().or(vec![left, right]);

        assert_eq!(
            result, expected,
            "\nExpected: {}\nGot: {}",
            expected, result
        );
    }

    #[test]
    fn test_nnf_nested() {
        let mut ctx = Context::default();

        // not(a /\ not(b \/ c)) should convert to not(a) \/ (b /\ c)
        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let c = ctx.temp_var(Sort::Bool);

        let var_a = ctx.ast().variable(a);
        let var_b = ctx.ast().variable(b);
        let var_c = ctx.ast().variable(c);

        let b_or_c = ctx.ast().or(vec![var_b.clone(), var_c.clone()]);
        let not_b_or_c = ctx.ast().not(b_or_c);
        let a_and_not_b_or_c = ctx.ast().and(vec![var_a.clone(), not_b_or_c]);
        let not_a_and_b_and_c = ctx.ast().not(a_and_not_b_or_c);

        // expected result is not(a) \/ (b /\ c)
        let not_a = ctx.ast().not(var_a);
        let b_and_c = ctx.ast().or(vec![var_b, var_c]);
        let expected = ctx.ast().or(vec![not_a, b_and_c]);

        let result = to_nnf(&not_a_and_b_and_c, &mut ctx);

        assert_eq!(
            result, expected,
            "\nExpected: {}\nGot: {}",
            expected, result
        );
    }
}
