use crate::node::{
    utils::{reverse, SymbolIterator},
    Node, NodeKind, NodeManager, Sorted,
};

use super::RewriteRule;

/// Fold trivial equations as follows:
/// - if the left-hand side and right-hand side are equal, return `true`
/// - if the left-hand side and right-hand side are both constants words and are not equal, return `false`
pub struct FoldTrivialEquations;

impl RewriteRule for FoldTrivialEquations {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            if lhs == rhs {
                return Some(mngr.ttrue());
            } else if let (NodeKind::String(lhs), NodeKind::String(rhs)) = (lhs.kind(), rhs.kind())
            {
                if lhs != rhs {
                    return Some(mngr.ffalse());
                }
            }
        }
        None
    }
}

/// Tries to strip the longest common constant prefix from the two sides of a word equation.
/// Let `lhs = rhs` be a word equation and p be the longest common prefix of lhs and rhs.
/// Then `lhs = p.lhs' and rhs = p.rhs'` for some lhs' and rhs'.
/// If p is non-empty, then the rule returns `lhs' = rhs'`.
pub struct WeqStripPrefix;

impl RewriteRule for WeqStripPrefix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            let mut lhs_iter = SymbolIterator::new(lhs);
            let mut rhs_iter = SymbolIterator::new(rhs);

            let mut i = 0;
            let mut next_lhs = lhs_iter.peek();
            let mut next_rhs = rhs_iter.peek();
            while next_lhs.is_some() && next_rhs.is_some() && next_lhs == next_rhs {
                i += 1;
                lhs_iter.next();
                rhs_iter.next();
                next_lhs = lhs_iter.peek();
                next_rhs = rhs_iter.peek();
            }

            if i > 0 {
                if lhs_iter.peek().is_none() && rhs_iter.peek().is_none() {
                    // Consumed the entire word, so the equation is trivially true
                    return Some(mngr.ttrue());
                } else {
                    let lhs_new = lhs_iter.to_node(mngr)?;
                    let rhs_new = rhs_iter.to_node(mngr)?;
                    return Some(mngr.eq(lhs_new, rhs_new));
                }
            }
        }
        None
    }
}

/// Same as `WeqStripPrefix`, but for suffixes.
pub struct WeqStripSuffix;

impl RewriteRule for WeqStripSuffix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq && node.children()[0].sort().is_string() {
            let reversed = reverse(node, mngr);
            let stripped_rev = WeqStripPrefix.apply(&reversed, mngr)?;
            Some(reverse(&stripped_rev, mngr))
        } else {
            None
        }
    }
}

/// If the equation is of the form `a.lhs = b.rhs` or `lhs.a = rhs.b` and `a != b`, then rewrite the equation to `false`.
pub struct WeqConstMismatch;

impl RewriteRule for WeqConstMismatch {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            // Check for first character mismatch
            if let (Some(lhs_char), Some(rhs_char)) = (first_char(lhs), first_char(rhs)) {
                if lhs_char != rhs_char {
                    return Some(mngr.ffalse());
                }
            }

            // Check for last character mismatch
            if let (Some(lhs_char), Some(rhs_char)) = (last_char(lhs), last_char(rhs)) {
                println!("lhs_char: {}, rhs_char: {}", lhs_char, rhs_char);
                if lhs_char != rhs_char {
                    return Some(mngr.ffalse());
                }
            }
        }
        None
    }
}

fn first_char(node: &Node) -> Option<char> {
    match node.kind() {
        NodeKind::String(s) => s.chars().next(),
        NodeKind::Concat => {
            let first_child = node.children().first()?;
            first_char(first_child)
        }
        _ => None,
    }
}

fn last_char(node: &Node) -> Option<char> {
    match node.kind() {
        NodeKind::String(s) => s.chars().last(),
        NodeKind::Concat => {
            let first_child = node.children().last()?;
            last_char(first_child)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::node::testutils::parse_equation;

    use super::*;

    #[test]
    fn test_strip_common_prefix_with_constants() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("abx", "aby", &mut mngr);
        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);
        let expected = parse_equation("x", "y", &mut mngr);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_strip_common_prefix_with_variables() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("abX", "abY", &mut mngr);
        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        let expected = parse_equation("X", "Y", &mut mngr);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_no_common_prefix_with_variables() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("aX", "bY", &mut mngr);

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // No common prefix, so no rewrite should happen
        assert_eq!(result, None);
    }

    #[test]
    fn test_strip_partial_prefix_with_variables() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("aX", "abcY", &mut mngr);
        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);
        let expected = parse_equation("X", "bcY", &mut mngr);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_exact_match_with_variables() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("abcX", "abcX", &mut mngr);
        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);
        let expected = mngr.ttrue();
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_mismatch_first_char() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("abcX", "yX", &mut mngr);

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in first characters "a" and "x"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_mismatch_last_char() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("Xab", "Xac", &mut mngr);

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in last characters "c" and "z"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_no_mismatch() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("Xab", "XaY", &mut mngr);
        assert!(WeqConstMismatch.apply(&equation, &mut mngr).is_none());
    }

    #[test]
    fn test_empty_lhs_rhs() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("", "", &mut mngr);
        assert!(WeqConstMismatch.apply(&equation, &mut mngr).is_none());
    }
}
