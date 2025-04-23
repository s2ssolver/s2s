mod string;

pub use string::*;

use crate::context::Context;

use super::{Node, NodeKind};

/// Reverse a node by reversing all children and the order of the children.
/// As a special case, if a node is a constant string, the string is reversed.
pub fn reverse(node: &Node, ctx: &mut Context) -> Node {
    match node.kind() {
        NodeKind::String(s) => {
            let revd = s.reversed();
            debug_assert_eq!(revd.len(), s.len());
            ctx.ast().const_string(revd)
        }
        _ => {
            let children = node
                .children()
                .iter()
                .rev()
                .map(|c| reverse(c, ctx))
                .collect();
            ctx.ast().create_node(node.kind().clone(), children)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::testutils::parse_pattern, context::Context};

    #[test]
    fn revers_concat() {
        let mut ctx = Context::default();
        let pattern_str = "abXcdYaX";
        let pattern_str_rev = "XaYdcXba";
        let pattern = parse_pattern(pattern_str, &mut ctx);
        let reversed = super::reverse(&pattern, &mut ctx);
        let expected = parse_pattern(pattern_str_rev, &mut ctx);
        assert_eq!(
            reversed, expected,
            "\nExpected: {}\nGot: {}",
            expected, reversed
        );
    }
}
