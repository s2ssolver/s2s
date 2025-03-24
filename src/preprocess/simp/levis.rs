use smt_str::SmtChar;

use crate::node::{
    utils::{reverse, PatternIterator, Symbol},
    NodeKind, Sorted,
};

use super::*;
/// Applies levi's rule to simplify word equations.
/// If the node is a word equation of the form "a\beta = Y\alpha" or "Y\alpha = a\beta" and Y cannot be set to the empty string without violating the equation,
/// then the rule infers that Y must start with 'a', i.e., will return the substitution "Y -> aY".
#[derive(Clone, Default)]
pub struct LevisWeq;

impl SimpRule for LevisWeq {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed && *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if lhs.sort().is_string() && rhs.sort().is_string() {
                if let Some(subs) = levis_step(lhs, rhs, mngr) {
                    return Some(Simplification::new(subs, None));
                } else {
                    let lhs_rev = reverse(lhs, mngr);
                    let rhs_rev = reverse(rhs, mngr);
                    if let Some(mut subs) = levis_step(&lhs_rev, &rhs_rev, mngr) {
                        // reverse subs
                        for (_, s) in subs.iter_mut() {
                            *s = reverse(s, mngr);
                        }
                        return Some(Simplification::new(subs, None));
                    }
                }
            }
        }
        None
    }

    fn name(&self) -> &str {
        "LevisLemma"
    }
}

fn levis_step(lhs: &Node, rhs: &Node, mngr: &mut NodeManager) -> Option<VarSubstitution> {
    /// Helper function to check if we have "a\beta = Y\alpha" or "Y\alpha = a\beta" and Y cannot be set to the empty string
    fn not_empty(constant: SmtChar, pattern: &mut PatternIterator) -> bool {
        let scnd = pattern.next();
        match scnd {
            Some(Symbol::Const(c)) => c != constant,
            None => true,
            _ => false,
        }
    }

    let mut lhs = PatternIterator::new(lhs);
    let mut rhs = PatternIterator::new(rhs);
    let mut substitution = VarSubstitution::default();
    match (lhs.next(), rhs.next()) {
        /* One side is constant, the other variable */
        (Some(Symbol::Const(c)), Some(Symbol::Variable(v))) if not_empty(c, &mut rhs) => {
            let prefix = mngr.const_string(c.into());
            let v_node = mngr.var(v.clone());
            let subs = mngr.concat(vec![prefix, v_node.clone()]);
            substitution.add(v, subs);
            Some(substitution)
        }
        (Some(Symbol::Variable(v)), Some(Symbol::Const(c))) if not_empty(c, &mut lhs) => {
            let prefix = mngr.const_string(c.into());
            let v_node = mngr.var(v.clone());
            let subs = mngr.concat(vec![prefix, v_node.clone()]);
            substitution.add(v.clone(), subs);
            Some(substitution)
        }
        // All other cases are either not reducible or already reduced by stripping common prefixes
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::testutils::parse_equation;

    #[test]
    fn test_levis_reducible_left() {
        let mut mngr = NodeManager::default();
        // Y must start with 'b'
        let eq = parse_equation("YaX", "bX", &mut mngr);
        let res = LevisWeq.apply(&eq, true, &mut mngr);

        assert!(res.is_some());
        let res = res.unwrap();

        let got = res.substitution().apply(&eq, &mut mngr);

        let expected = parse_equation("bYaX", "bX", &mut mngr);
        assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
    }

    #[test]
    fn test_levis_reducible_right() {
        let mut mngr = NodeManager::default();
        // Y must start with 'b'
        let eq = parse_equation("bX", "YaX", &mut mngr);
        let res = LevisWeq.apply(&eq, true, &mut mngr);

        assert!(res.is_some());
        let res = res.unwrap();

        let got = res.substitution().apply(&eq, &mut mngr);
        let expected = parse_equation("bX", "bYaX", &mut mngr);
        assert_eq!(got, expected, "\nExpected: {}, \nGot: {}", expected, got);
    }

    #[test]
    fn test_levis_not_reducible_left() {
        let mut mngr = NodeManager::default();
        // Y could start with 'b' or be empty
        let eq = parse_equation("YaX", "aX", &mut mngr);
        let res = LevisWeq.apply(&eq, true, &mut mngr);

        assert!(res.is_none());
    }

    #[test]
    fn test_levis_not_reducible_right() {
        let mut mngr = NodeManager::default();
        // Y could start with 'b' or be empty
        let eq = parse_equation("aX", "YaX", &mut mngr);
        let res = LevisWeq.apply(&eq, true, &mut mngr);

        assert!(res.is_none());
    }
}
