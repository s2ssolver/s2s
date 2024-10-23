use crate::node::{Node, NodeKind, NodeManager};

use super::RewriteRule;

/// Tries to strip the longest common constant prefix from the two sides of a word equation.
/// Let `lhs = rhs` be a word equation and p be the longest common prefix of lhs and rhs.
/// Then `lhs = p.lhs' and rhs = p.rhs'` for some lhs' and rhs'.
/// If p is non-empty, then the rule returns `lhs' = rhs'`.
/// A special case is when lhs = rhs, in which case the rule returns `true`.
pub struct WeqStripPrefix;

impl RewriteRule for WeqStripPrefix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            // Attempt to patternize both sides of the equation
            let lhs_pattern = mngr.patternize(lhs)?;
            let rhs_pattern = mngr.patternize(rhs)?;

            // Find the longest common prefix
            let mut i = 0;
            while i < lhs_pattern.len() && i < rhs_pattern.len() && lhs_pattern[i] == rhs_pattern[i]
            {
                i += 1;
            }

            if i > 0 {
                if i == lhs_pattern.len() && i == rhs_pattern.len() {
                    // If the common prefix is the entire word, then the equation is trivially true
                    return Some(mngr.ttrue());
                }

                // Strip the common prefix and depatternize the remaining parts
                let stripped_lhs = lhs_pattern.strip_prefix(i);
                let stripped_rhs = rhs_pattern.strip_prefix(i);

                let new_lhs = mngr.depatternize(&stripped_lhs);
                let new_rhs = mngr.depatternize(&stripped_rhs);

                // Return the new equation without the common prefix
                return Some(mngr.eq(new_lhs, new_rhs));
            }
        }
        None
    }
}

/// Same as `WeqStripPrefix`, but for suffixes.
pub struct WeqStripSuffix;

impl RewriteRule for WeqStripSuffix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            let rhs = &node.children()[1];

            // Attempt to patternize both sides of the equation
            let lhs_pattern = mngr.patternize(lhs)?;
            let rhs_pattern = mngr.patternize(rhs)?;

            // Find the longest common prefix
            let mut i = 1;
            let lhs_len = lhs_pattern.len();
            let rhs_len = rhs_pattern.len();
            while i <= lhs_pattern.len()
                && i <= rhs_pattern.len()
                && lhs_pattern[lhs_len - i] == rhs_pattern[rhs_len - i]
            {
                i += 1;
            }

            if i > 0 {
                if i == lhs_pattern.len() && i == rhs_pattern.len() {
                    // If the common prefix is the entire word, then the equation is trivially true
                    return Some(mngr.ttrue());
                }

                // Strip the common prefix and depatternize the remaining parts
                let stripped_lhs = lhs_pattern.strip_suffix(i);
                let stripped_rhs = rhs_pattern.strip_suffix(i);

                let new_lhs = mngr.depatternize(&stripped_lhs);
                let new_rhs = mngr.depatternize(&stripped_rhs);

                // Return the new equation without the common prefix
                return Some(mngr.eq(new_lhs, new_rhs));
            }
        }
        None
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
            for child in node.children() {
                if let Some(c) = first_char(child) {
                    return Some(c);
                }
            }
            None
        }
        _ => None,
    }
}

fn last_char(node: &Node) -> Option<char> {
    match node.kind() {
        NodeKind::String(s) => s.chars().last(),
        NodeKind::Concat => {
            for child in node.children().iter().rev() {
                if let Some(c) = last_char(child) {
                    return Some(c);
                }
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::context::{Context, Sort};

    use super::*;

    #[test]
    fn test_strip_common_prefix_with_constants() {
        let mut mngr = NodeManager::default();

        // Test case where lhs and rhs have a common prefix "ab"
        let lhs = mngr.const_str("abx");
        let rhs = mngr.const_str("aby");

        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `x = y` after stripping the common prefix "ab"
        let expected_lhs = mngr.const_str("x");
        let expected_rhs = mngr.const_str("y");
        let expected = mngr.eq(expected_lhs, expected_rhs);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_strip_common_prefix_with_variables() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where lhs and rhs have a common prefix "ab"
        let var_x = ctx.new_temp_var(Sort::String);
        let var_y = ctx.new_temp_var(Sort::String);

        let lhs_str_ab = mngr.const_str("ab");
        let lhs_var_x = mngr.var(var_x.clone());
        let rhs_str_ab = mngr.const_str("ab");
        let rhs_var_y = mngr.var(var_y.clone());

        let lhs = mngr.concat(vec![lhs_str_ab, lhs_var_x]);
        let rhs = mngr.concat(vec![rhs_str_ab, rhs_var_y]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `x = y` after stripping the common prefix "ab"
        let expected_lhs = mngr.var(var_x);
        let expected_rhs = mngr.var(var_y);
        let expected = mngr.eq(expected_lhs, expected_rhs);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_no_common_prefix_with_variables() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where lhs and rhs have no common prefix
        let var_x = ctx.new_temp_var(Sort::String);
        let var_y = ctx.new_temp_var(Sort::String);

        let lhs_str_a = mngr.const_str("a");
        let lhs_var_x = mngr.var(var_x);
        let rhs_str_b = mngr.const_str("b");
        let rhs_var_y = mngr.var(var_y);

        let lhs = mngr.concat(vec![lhs_str_a, lhs_var_x]);
        let rhs = mngr.concat(vec![rhs_str_b, rhs_var_y]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // No common prefix, so no rewrite should happen
        assert_eq!(result, None);
    }

    #[test]
    fn test_strip_partial_prefix_with_variables() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where lhs and rhs have a partial common prefix with variables
        let var_x = ctx.new_temp_var(Sort::String);
        let var_y = ctx.new_temp_var(Sort::String);

        let lhs_str_a = mngr.const_str("a");
        let lhs_var_x = mngr.var(var_x.clone());
        let rhs_str_abc = mngr.const_str("abc");
        let var_y = mngr.var(var_y.clone());

        let lhs = mngr.concat(vec![lhs_str_a, lhs_var_x]);
        let rhs = mngr.concat(vec![rhs_str_abc, var_y.clone()]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `x = y` after stripping the common prefix "abc"

        let expected_lhs = mngr.var(var_x);
        let str_bc = mngr.const_str("bc");
        let expected_rhs = mngr.concat(vec![str_bc, var_y]);
        let expected = mngr.eq(expected_lhs, expected_rhs);

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_exact_match_with_variables() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where lhs and rhs are exactly the same
        let var_x = ctx.new_temp_var(Sort::String);
        let var_x_node = mngr.var(var_x);
        let str_abc = mngr.const_str("abc");

        let lhs = mngr.concat(vec![str_abc.clone(), var_x_node.clone()]);
        let rhs = mngr.concat(vec![str_abc.clone(), var_x_node.clone()]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqStripPrefix;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `true` since the equation is trivially true
        let expected = mngr.ttrue();

        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_mismatch_first_char() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where first characters of lhs and rhs differ
        let abc = mngr.const_str("abc");
        let xyz = mngr.const_str("xyz");
        let x = mngr.var(ctx.new_temp_var(Sort::String));
        let y = mngr.var(ctx.new_temp_var(Sort::String));
        let lhs = mngr.concat(vec![abc, x]);
        let rhs = mngr.concat(vec![xyz, y]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in first characters "a" and "x"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_mismatch_last_char() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where first characters of lhs and rhs differ
        let abc = mngr.const_str("abc");
        let xyz = mngr.const_str("xyz");
        let x = mngr.var(ctx.new_temp_var(Sort::String));
        let y = mngr.var(ctx.new_temp_var(Sort::String));
        let lhs = mngr.concat(vec![x, abc]);
        let rhs = mngr.concat(vec![y, xyz]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // Expect the result to be `false` due to mismatch in last characters "c" and "z"
        assert_eq!(result, Some(mngr.ffalse()));
    }

    #[test]
    fn test_no_mismatch() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();

        // Test case where first and last characters of lhs and rhs match
        let abc = mngr.const_str("abc");
        let x = mngr.var(ctx.new_temp_var(Sort::String));
        let y = mngr.var(ctx.new_temp_var(Sort::String));
        let lhs = mngr.concat(vec![abc.clone(), x]);
        let rhs = mngr.concat(vec![abc.clone(), y]);
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // No mismatch, so the result should be None (no rewrite)
        assert_eq!(result, None);
    }

    #[test]
    fn test_empty_lhs_rhs() {
        // Edge case test where both lhs and rhs are empty strings
        let mut mngr = NodeManager::default();

        // Test case where both lhs and rhs are empty strings
        let lhs = mngr.const_str("");
        let rhs = mngr.const_str("");
        let equation = mngr.eq(lhs.clone(), rhs.clone());

        let rule = WeqConstMismatch;
        let result = rule.apply(&equation, &mut mngr);

        // No mismatch, both sides are empty, so no rewrite should happen
        assert_eq!(result, None);
    }
}
