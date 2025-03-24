mod string;

pub use string::*;

use super::{Node, NodeKind, NodeManager};

/// Reverse a node by reversing all children and the order of the children.
/// As a special case, if a node is a constant string, the string is reversed.
pub fn reverse(node: &Node, mngr: &mut NodeManager) -> Node {
    match node.kind() {
        NodeKind::String(s) => {
            let revd = s.reversed();
            debug_assert_eq!(revd.len(), s.len());
            mngr.const_string(revd)
        }
        _ => {
            let children = node
                .children()
                .iter()
                .rev()
                .map(|c| reverse(c, mngr))
                .collect();
            mngr.create_node(node.kind().clone(), children)
        }
    }
}

#[cfg(test)]
mod test {
    use crate::node::{testutils::parse_pattern, NodeManager};

    #[test]
    fn revers_concat() {
        let mut mngr = NodeManager::default();
        let pattern_str = "abXcdYaX";
        let pattern_str_rev = "XaYdcXba";
        let pattern = parse_pattern(pattern_str, &mut mngr);
        let reversed = super::reverse(&pattern, &mut mngr);
        let expected = parse_pattern(pattern_str_rev, &mut mngr);
        assert_eq!(
            reversed, expected,
            "\nExpected: {}\nGot: {}",
            expected, reversed
        );
    }
}
