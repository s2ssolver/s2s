use smt_str::{SmtChar, SmtString};

use crate::{
    ast::{
        utils::{reverse, PatternIterator, Symbol},
        NodeKind,
    },
    context::Sorted,
};

use super::*;
/// Applies levi's rule to simplify word equations.
/// If the node is a word equation of the form "a\beta = Y\alpha" or "Y\alpha = a\beta" and Y cannot be set to the empty string without violating the equation,
/// then the rule infers that Y must start with 'a', i.e., will return the substitution "Y -> aY".
#[derive(Clone, Default, Debug)]
pub(super) struct LevisRule;

impl EntailmentRule for LevisRule {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        _: bool,
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        // This is only applicable if the node itself is asserted
        if !asserted.contains(node) {
            return None;
        }
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if lhs.sort().is_string() && rhs.sort().is_string() {
                if let Some(subs) = levis_step(lhs, rhs, ctx) {
                    return Some(subs);
                } else {
                    let lhs_rev = reverse(lhs, ctx);
                    let rhs_rev = reverse(rhs, ctx);
                    if let Some(mut subs) = levis_step(&lhs_rev, &rhs_rev, ctx) {
                        // reverse subs
                        for (_, s) in subs.iter_mut() {
                            *s = reverse(s, ctx);
                        }
                        return Some(subs);
                    }
                }
            }
        }
        None
    }
}

fn levis_step(lhs: &Node, rhs: &Node, ctx: &mut Context) -> Option<VarSubstitution> {
    /// Helper function to check if we have "a\beta = Y\alpha" or "Y\alpha = a\beta" and Y cannot be set to the empty string
    fn not_empty(constant: SmtChar, pattern: &PatternIterator) -> bool {
        let scnd = pattern.peek();
        match scnd {
            Some(Symbol::Const(c)) => c != constant,
            None => true,
            _ => false,
        }
    }

    let mut lhs_iter = PatternIterator::new(lhs);
    let mut rhs_iter = PatternIterator::new(rhs);
    let mut substitution = VarSubstitution::default();

    match (lhs_iter.peek(), rhs_iter.next()) {
        (Some(Symbol::Const(_)), Some(Symbol::Variable(v))) => {
            let mut prefix = SmtString::empty();
            let v_node = ctx.ast().variable(v.clone());
            while let Some(Symbol::Const(c)) = lhs_iter.next() {
                if not_empty(c, &rhs_iter) {
                    prefix.push(c);
                } else {
                    break;
                }
            }
            if !prefix.is_empty() {
                let prefix = ctx.ast().const_string(prefix);
                let sub = ctx.ast().concat(vec![prefix, v_node.clone()]);
                substitution.add(v.clone(), sub);
                return Some(substitution);
            }
        }
        (Some(Symbol::Variable(_)), Some(Symbol::Const(_))) => {
            // flip lhs and rhs
            return levis_step(rhs, lhs, ctx);
        }
        _ => (),
    }
    None
}

#[cfg(test)]
mod tests {
    use indexmap::indexset;

    use super::*;
    use crate::ast::testutils::parse_equation;

    #[test]
    fn test_levis_reducible_left_char() {
        let mut ctx = Context::default();
        // Y must start with 'b'
        let eq = parse_equation("YaX", "bX", &mut ctx);
        let asserted = indexset! {eq.clone()};
        let res = LevisRule.apply(&eq, &asserted, true, &mut ctx);

        match res {
            Some(got) => {
                let got = got.apply(&eq, &mut ctx);
                let expected = parse_equation("bYaX", "bX", &mut ctx);
                assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_levis_reducible_left_word() {
        let mut ctx = Context::default();
        // Y must start with 'b'
        let eq = parse_equation("YaX", "fooX", &mut ctx);
        let asserted = indexset! {eq.clone()};
        let res = LevisRule.apply(&eq, &asserted, true, &mut ctx);

        match res {
            Some(got) => {
                let got = got.apply(&eq, &mut ctx);
                let expected = parse_equation("fooYaX", "fooX", &mut ctx);
                assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_levis_reducible_right_char() {
        let mut ctx = Context::default();
        // Y must start with 'b'
        let eq = parse_equation("bX", "YaX", &mut ctx);
        let asserted = indexset! {eq.clone()};
        let res = LevisRule.apply(&eq, &asserted, true, &mut ctx);

        match res {
            Some(got) => {
                let got = got.apply(&eq, &mut ctx);
                let expected = parse_equation("bX", "bYaX", &mut ctx);
                assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_levis_reducible_right_word() {
        let mut ctx = Context::default();
        // Y must start with 'b'
        let eq = parse_equation("fooX", "YaX", &mut ctx);
        let asserted = indexset! {eq.clone()};
        let res = LevisRule.apply(&eq, &asserted, true, &mut ctx);

        match res {
            Some(got) => {
                let got = got.apply(&eq, &mut ctx);
                let expected = parse_equation("fooX", "fooYaX", &mut ctx);
                assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_levis_not_reducible_left() {
        let mut ctx = Context::default();
        // Y could start with 'b' or be empty
        let eq = parse_equation("YaX", "aX", &mut ctx);
        let res = LevisRule.apply(&eq, &IndexSet::new(), true, &mut ctx);

        assert!(res.is_none());
    }

    #[test]
    fn test_levis_not_reducible_right() {
        let mut ctx = Context::default();
        // Y could start with 'b' or be empty
        let eq = parse_equation("aX", "YaX", &mut ctx);
        let res = LevisRule.apply(&eq, &IndexSet::new(), true, &mut ctx);

        assert!(res.is_none());
    }
}
