use indexmap::IndexMap;
use num_integer::Integer;
use smtlib_str::SmtChar;

use crate::node::{
    utils::{reverse, PatternIterator, Symbol},
    Node, NodeKind, NodeManager, Sorted,
};

/// Tries to strip the longest common constant prefix from the two sides of a word equation.
/// Let `p.lhs = p.rhs` be a word equation and p be the longest common prefix of both sides.
/// If p is non-empty, then the rule returns `lhs' = rhs'`.
pub fn strip_lcp(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Eq && node.children()[0].sort().is_string() {
        debug_assert!(node.children().len() == 2);
        debug_assert!(node.children()[0].sort().is_string());
        debug_assert!(node.children()[1].sort().is_string());
        let mut lhs_iter = PatternIterator::new(&node.children()[0]);
        let mut rhs_iter = PatternIterator::new(&node.children()[1]);

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

        return if i > 0 {
            let lhs_new = lhs_iter.to_node(mngr)?;
            let rhs_new = rhs_iter.to_node(mngr)?;
            Some(mngr.eq(lhs_new, rhs_new))
        } else {
            None
        };
    }
    None
}

/// Same as `strip_lcp`, but for suffixes.
pub fn strip_lcs(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Eq && node.children()[0].sort().is_string() {
        let reversed = reverse(node, mngr);
        let stripped_rev = strip_lcp(&reversed, mngr)?;
        Some(reverse(&stripped_rev, mngr))
    } else {
        None
    }
}

/// Checks whether the equation is of the form `a.lhs = b.rhs` or `lhs.a = rhs.b` and `a != b`.
/// If so, returns `false`.
pub fn const_mismatch(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Eq {
        debug_assert!(node.children().len() == 2);
        let lhs = &node.children()[0];
        let rhs = &node.children()[1];

        // Check for first character mismatch
        match (first_char(lhs), first_char(rhs)) {
            (Some(lhs_char), Some(rhs_char)) if lhs_char != rhs_char => {
                return Some(mngr.ffalse());
            }
            (Some(_), None) if is_empty_string(rhs) => return Some(mngr.ffalse()),
            (None, Some(_)) if is_empty_string(lhs) => return Some(mngr.ffalse()),

            _ => {}
        }

        // Check for last character mismatch
        if let (Some(lhs_char), Some(rhs_char)) = (last_char(lhs), last_char(rhs)) {
            if lhs_char != rhs_char {
                return Some(mngr.ffalse());
            }
        }
    }
    None
}

/// Reasons on the length abstraction of the word equation.
/// If the length abstraction is |x_1|c_1 + |x_2|c_2 + ... + |x_n|c_n = b, then it is unsatisfiable if:
/// - b is odd and all coefficients are even
/// - gcd(c_1, c_2, ..., c_n) does not divide b
/// - all coefficients are 0 but b is non-zero
/// - all coefficients are negative but b is positive
/// - all coefficients are positive but b is negative
pub fn length_reasoning(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Eq {
        debug_assert!(node.children().len() == 2);
        let lhs = &node.children()[0];
        let rhs = &node.children()[1];

        let lhs_iter = PatternIterator::new(lhs);
        let rhs_iter = PatternIterator::new(rhs);

        let mut coeffs: IndexMap<std::rc::Rc<crate::node::Variable>, i32> = IndexMap::new();
        let mut r: i32 = 0;

        for s in lhs_iter {
            match s {
                Symbol::Const(_) => r -= 1,
                Symbol::Variable(v) => *coeffs.entry(v).or_insert(0) += 1,
                Symbol::Other(_) => return None,
            }
        }
        for s in rhs_iter {
            match s {
                Symbol::Const(_) => r += 1,
                Symbol::Variable(v) => *coeffs.entry(v).or_insert(0) -= 1,
                Symbol::Other(_) => return None,
            }
        }
        // Check if the equation is trivially unsatisfiable

        // Parity condition
        if r % 2 != 0 && coeffs.values().all(|&c| (c.abs() as u64) % 2 == 0) {
            return Some(mngr.ffalse());
        }

        // lefthand-side is 0 but right-hand-side is non-zero
        if r != 0 && (coeffs.values().all(|&c| c == 0) || coeffs.is_empty()) {
            return Some(mngr.ffalse());
        }

        // All coefficients < 0 but the constant term is positive
        if r > 0 && coeffs.values().all(|&c| c < 0) {
            return Some(mngr.ffalse());
        }

        // All coefficients >= 0 but the constant term is negative
        if r < 0 && coeffs.values().all(|&c| c >= 0) {
            return Some(mngr.ffalse());
        }

        // Divisibility condition: gcd(c_1, c_2, ..., c_n) divides b
        if !coeffs.is_empty() && r != 0 {
            let gcd = coeffs.values().fold(0, |a: i32, &b| a.gcd(&b.abs()));
            if r % gcd != 0 {
                return Some(mngr.ffalse());
            }
        }
    }
    None
}

/// Returns `true` if the node is a string node with an empty string.
fn is_empty_string(node: &Node) -> bool {
    match node.kind() {
        NodeKind::String(s) => s.is_empty(),
        NodeKind::Concat => {
            node.children().is_empty() || node.children().iter().all(is_empty_string)
        }
        _ => false,
    }
}

/// If the node is a pattern starting with a constant character, return that character.
/// Otherwise, return `None`.
fn first_char(node: &Node) -> Option<SmtChar> {
    match node.kind() {
        NodeKind::String(s) => s.first(),
        NodeKind::Concat => {
            let first_child = node.children().first()?;
            first_char(first_child)
        }
        _ => None,
    }
}

/// If the node is a pattern ending with a constant character, return that character.
/// Otherwise, return `None`.
fn last_char(node: &Node) -> Option<SmtChar> {
    match node.kind() {
        NodeKind::String(s) => s.last(),
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
        let result = strip_lcp(&equation, &mut mngr);
        let expected = parse_equation("x", "y", &mut mngr);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_strip_common_prefix_with_variables() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("abX", "abY", &mut mngr);
        let result = strip_lcp(&equation, &mut mngr);

        let expected = parse_equation("X", "Y", &mut mngr);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_no_common_prefix_with_variables() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("aX", "bY", &mut mngr);

        let result = strip_lcp(&equation, &mut mngr);

        // No common prefix, so no rewrite should happen
        assert_eq!(result, None);
    }

    #[test]
    fn test_strip_partial_prefix_with_variables() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("aX", "abcY", &mut mngr);

        let result = strip_lcp(&equation, &mut mngr);
        let expected = parse_equation("X", "bcY", &mut mngr);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_mismatch_first_char() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("abcX", "yX", &mut mngr);

        let result = const_mismatch(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in first characters "a" and "x"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_mismatch_last_char() {
        let mut mngr = NodeManager::default();
        let equation = parse_equation("Xab", "Xac", &mut mngr);

        let result = const_mismatch(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in last characters "c" and "z"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_no_mismatch() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("Xab", "XaY", &mut mngr);
        assert!(const_mismatch(&equation, &mut mngr).is_none());
    }

    #[test]
    fn test_empty_lhs_rhs() {
        let mut mngr = NodeManager::default();

        let equation = parse_equation("", "", &mut mngr);
        assert!(const_mismatch(&equation, &mut mngr).is_none());
    }
}
