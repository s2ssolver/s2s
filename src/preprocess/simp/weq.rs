use std::rc::Rc;

use super::*;
use crate::{
    ast::{
        utils::{reverse, PatternIterator, Symbol},
        Node, NodeKind,
    },
    context::{Sorted, Variable},
};
use indexmap::IndexMap;
use num_integer::Integer;

use smt_str::SmtChar;

/// Tries to strip the longest common constant prefix from the two sides of a word equation.
/// Let `p.lhs = p.rhs` be a word equation and p be the longest common prefix of both sides.
/// If p is non-empty, then the rule returns `lhs' = rhs'`.
#[derive(Debug, Clone, Copy)]
pub(super) struct StripLCP;
impl EquivalenceRule for StripLCP {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
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

            if i > 0 {
                let lhs_new = lhs_iter.to_node(ctx)?;
                let rhs_new = rhs_iter.to_node(ctx)?;
                return Some(ctx.ast().eq(lhs_new, rhs_new));
            }
        }
        None
    }
}

/// Same as `strip_lcp`, but for suffixes.
#[derive(Debug, Clone, Copy)]
pub(super) struct StripLCS;
impl EquivalenceRule for StripLCS {
    fn apply(&self, node: &Node, a: bool, pa: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Eq && node.children()[0].sort().is_string() {
            let reversed = reverse(node, ctx);
            if let Some(stripped_rev) = StripLCP.apply(&reversed, a, pa, ctx) {
                return Some(reverse(&stripped_rev, ctx));
            };
        }
        None
    }
}

/// Checks whether the equation is of the form `a.lhs = b.rhs` or `lhs.a = rhs.b` and `a != b`.
/// If so, returns `false`.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConstMismatch;
impl EquivalenceRule for ConstMismatch {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            // Check for first character mismatch
            match (first_char(lhs), first_char(rhs)) {
                (Some(lhs_char), Some(rhs_char)) if lhs_char != rhs_char => {
                    return Some(ctx.ast().ffalse());
                }
                (Some(_), None) if is_empty_string(rhs) => return Some(ctx.ast().ffalse()),
                (None, Some(_)) if is_empty_string(lhs) => return Some(ctx.ast().ffalse()),

                _ => {}
            }

            // Check for last character mismatch
            if let (Some(lhs_char), Some(rhs_char)) = (last_char(lhs), last_char(rhs)) {
                if lhs_char != rhs_char {
                    return Some(ctx.ast().ffalse());
                }
            }
        }
        None
    }
}

/// Reasons on the length abstraction of the word equation.
/// If the length abstraction is |x_1|c_1 + |x_2|c_2 + ... + |x_n|c_n = b, then it is unsatisfiable if:
/// - b is odd and all coefficients are even
/// - gcd(c_1, c_2, ..., c_n) does not divide b
/// - all coefficients are 0 but b is non-zero
/// - all coefficients are negative but b is positive
/// - all coefficients are positive but b is negative
#[derive(Debug, Clone, Copy)]
pub(super) struct LengthReasoning;
impl EquivalenceRule for LengthReasoning {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            let lhs_iter = PatternIterator::new(lhs);
            let rhs_iter = PatternIterator::new(rhs);

            let mut coeffs: IndexMap<Rc<Variable>, i32> = IndexMap::new();
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
            if r % 2 != 0 && coeffs.values().all(|&c| (c.unsigned_abs() as u64) % 2 == 0) {
                return Some(ctx.ast().ffalse());
            }

            // lefthand-side is 0 but right-hand-side is non-zero
            if r != 0 && (coeffs.values().all(|&c| c == 0) || coeffs.is_empty()) {
                return Some(ctx.ast().ffalse());
            }

            // All coefficients < 0 but the constant term is positive
            if r > 0 && coeffs.values().all(|&c| c < 0) {
                return Some(ctx.ast().ffalse());
            }

            // All coefficients >= 0 but the constant term is negative
            if r < 0 && coeffs.values().all(|&c| c >= 0) {
                return Some(ctx.ast().ffalse());
            }

            // Divisibility condition: gcd(c_1, c_2, ..., c_n) divides b
            if !coeffs.is_empty() && r != 0 {
                let gcd = coeffs.values().fold(0, |a: i32, &b| a.gcd(&b.abs()));
                if r % gcd != 0 {
                    return Some(ctx.ast().ffalse());
                }
            }
        }
        None
    }
}

/// Computes the Parikh matrix of both sides of the equation.
/// If there is a prefix of length `i` that has the same occurrences variables but different constants, then the equation is unsatisfiable.
/// For example `aX = Xb` is unsatisfiable because `a` and `b` are different constants but `X` is the same variable.
/// These prefixes are obtained using the parikh matrix.
#[derive(Debug, Clone, Copy)]
pub(super) struct ParikhMatrixMismatch;

impl ParikhMatrixMismatch {
    fn is_unsat(lhs: impl Iterator<Item = Symbol>, rhs: impl Iterator<Item = Symbol>) -> bool {
        let mut lhs_map: IndexMap<Symbol, u32> = IndexMap::new();
        let mut rhs_map: IndexMap<Symbol, u32> = IndexMap::new();
        let mut keys = IndexSet::new();

        for (lhs_symbol, rhs_symbol) in lhs.zip(rhs) {
            if lhs_symbol.is_other() || rhs_symbol.is_other() {
                return false;
            }

            *lhs_map.entry(lhs_symbol.clone()).or_insert(0) += 1;
            *rhs_map.entry(rhs_symbol.clone()).or_insert(0) += 1;
            keys.insert(lhs_symbol);
            keys.insert(rhs_symbol);

            let mut constant_mismatch = false;
            let mut variable_mismatch = false;
            for k in &keys {
                let lhs_count = lhs_map.get(k).unwrap_or(&0);
                let rhs_count = rhs_map.get(k).unwrap_or(&0);
                if lhs_count != rhs_count {
                    if k.is_variable() {
                        variable_mismatch = true;
                    } else {
                        constant_mismatch = true;
                    }
                }
            }
            if constant_mismatch && !variable_mismatch {
                return true;
            }
        }
        false
    }
}

impl EquivalenceRule for ParikhMatrixMismatch {
    fn apply(&self, node: &Node, _: bool, _: &IndexSet<Node>, ctx: &mut Context) -> Option<Node> {
        if node.kind() == &NodeKind::Eq {
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];
            if !lhs.sort().is_string() || !rhs.sort().is_string() {
                return None;
            }

            let lhs_iter = PatternIterator::new(lhs);
            let rhs_iter = PatternIterator::new(rhs);

            if Self::is_unsat(lhs_iter, rhs_iter) {
                return Some(ctx.ast().ffalse());
            }

            // Check for suffix mismatch

            let reversed_lhs = reverse(lhs, ctx);
            let lhs_iter = PatternIterator::new(&reversed_lhs);
            let reversed_rhs = reverse(rhs, ctx);
            let rhs_iter = PatternIterator::new(&reversed_rhs);
            if Self::is_unsat(lhs_iter, rhs_iter) {
                return Some(ctx.ast().ffalse());
            }
        }
        None
    }
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
    use crate::ast::testutils::parse_equation;

    use super::*;

    #[test]
    fn test_strip_common_prefix_with_constants() {
        let mut ctx = Context::default();
        ctx.ast().set_simplify(false);

        let equation = parse_equation("abx", "aby", &mut ctx);
        let result = StripLCP.apply(&equation, true, &IndexSet::new(), &mut ctx);
        let expected = parse_equation("x", "y", &mut ctx);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_strip_common_prefix_with_variables() {
        let mut ctx = Context::default();
        let equation = parse_equation("abX", "abY", &mut ctx);
        let result = StripLCP.apply(&equation, true, &IndexSet::new(), &mut ctx);

        let expected = parse_equation("X", "Y", &mut ctx);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_no_common_prefix_with_variables() {
        let mut ctx = Context::default();

        let equation = parse_equation("aX", "bY", &mut ctx);

        let result = StripLCP.apply(&equation, true, &IndexSet::new(), &mut ctx);

        // No common prefix, so no rewrite should happen
        assert_eq!(result, None);
    }

    #[test]
    fn test_strip_partial_prefix_with_variables() {
        let mut ctx = Context::default();
        let equation = parse_equation("aX", "abcY", &mut ctx);

        let result = StripLCP.apply(&equation, true, &IndexSet::new(), &mut ctx);
        let expected = parse_equation("X", "bcY", &mut ctx);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_mismatch_first_char() {
        let mut ctx = Context::default();
        let equation = parse_equation("abcX", "yX", &mut ctx);

        let result = ConstMismatch.apply(&equation, true, &IndexSet::new(), &mut ctx);

        // Expect the result to be `false` due to mismatch in first characters "a" and "x"
        assert_eq!(result, Some(ctx.ast().ffalse()));
    }

    #[test]
    fn test_mismatch_last_char() {
        let mut ctx = Context::default();
        let equation = parse_equation("Xab", "Xac", &mut ctx);

        let result = ConstMismatch.apply(&equation, true, &IndexSet::new(), &mut ctx);

        assert_eq!(result, Some(ctx.ast().ffalse()));
    }

    #[test]
    fn test_no_mismatch() {
        let mut ctx = Context::default();

        let equation = parse_equation("Xab", "XaY", &mut ctx);

        let result = ConstMismatch.apply(&equation, true, &IndexSet::new(), &mut ctx);

        assert_eq!(result, None);
    }

    #[test]
    fn test_empty_lhs_rhs() {
        let mut ctx = Context::default();

        let equation = parse_equation("", "", &mut ctx);

        let result = ConstMismatch.apply(&equation, true, &IndexSet::new(), &mut ctx);

        assert_eq!(result, None);
    }
}
