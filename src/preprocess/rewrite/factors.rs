use itertools::Itertools;

use crate::node::{
    utils::{reverse, PatternIterator},
    Node, NodeKind, NodeManager,
};

// Folds prefixof(x, y) into true if x is a prefix of y.
pub fn trivial_prefixof(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::PrefixOf {
        debug_assert!(node.children().len() == 2);
        let lhs = &node.children()[0];
        let rhs = &node.children()[1];
        // Only works if both lhs and rhs are patterns.
        match lhs.kind() {
            NodeKind::Variable(_) | NodeKind::String(_) | NodeKind::Concat => match rhs.kind() {
                NodeKind::Variable(_) | NodeKind::String(_) | NodeKind::Concat => {
                    let mut rhs_symbols = PatternIterator::new(rhs);
                    let lhs_symbols = PatternIterator::new(lhs);

                    for s in lhs_symbols {
                        if Some(s) != rhs_symbols.next() {
                            return None;
                        }
                    }
                    // If we reached the end of lhs, then lhs is a prefix of rhs.
                    return Some(mngr.ttrue());
                }
                _ => {}
            },
            _ => {}
        }
    }
    None
}

pub fn trivial_suffixof(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::SuffixOf {
        let lhs = &node.children()[0];
        let rhs = &node.children()[1];
        let r_lhs = reverse(lhs, mngr);
        let r_rhs = reverse(rhs, mngr);
        let prefixof = &mngr.prefix_of(r_lhs, r_rhs);
        return trivial_prefixof(prefixof, mngr);
    }
    None
}

/// Folds contains(x, y)
/// - into true if x contains y
/// - into false if x does not contain y and both x and y are constant strings
pub fn trivial_contains(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Contains {
        let haystack = &node.children()[0];
        let needle = &node.children()[1];

        // Only works if both haystack and needle are patterns.
        match haystack.kind() {
            NodeKind::Variable(_) | NodeKind::String(_) | NodeKind::Concat => match needle.kind() {
                NodeKind::Variable(_) | NodeKind::String(_) | NodeKind::Concat => {
                    let haystack = PatternIterator::new(haystack).collect_vec();
                    let needle = PatternIterator::new(needle).collect_vec();

                    if find_subvec(&haystack, &needle) {
                        return Some(mngr.ttrue());
                    } else if haystack.iter().all(|s| s.is_const())
                        && needle.iter().all(|s| s.is_const())
                    {
                        return Some(mngr.ffalse());
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    None
}

fn find_subvec<T: PartialEq>(mut haystack: &[T], needle: &[T]) -> bool {
    if needle.len() == 0 {
        return true;
    }
    while !haystack.is_empty() {
        if haystack.starts_with(needle) {
            return true;
        }
        haystack = &haystack[1..];
    }
    false
}
