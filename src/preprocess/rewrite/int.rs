use crate::node::{NodeKind, Sorted};

use super::*;

/// Fold constant integer terms. If i1, i2, ..., in are integer constants, then:
/// - +(i1, i2, ..., in) -> i1 + i2 + ... + in
/// - -(i1, i2, ..., in) -> i1 - i2 - ... - in
/// - *(i1, i2, ..., in) -> i1 * i2 * ... * in
pub fn fold_constant_ints(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if node.sort().is_int() {
        // Fold constant terms
        match node.kind() {
            NodeKind::Add => {
                let mut sum = 0;
                let mut folded = 0;
                let mut new_children = Vec::new();
                for child in node.children() {
                    match child.kind() {
                        NodeKind::Int(i) => {
                            sum += i;
                            folded += 1;
                        }
                        _ => {
                            new_children.push(child.clone());
                        }
                    }
                }
                if folded > 1 {
                    let sum_node = mngr.const_int(sum);
                    new_children.push(sum_node);
                    Some(mngr.add(new_children))
                } else {
                    None
                }
            }
            NodeKind::Sub => {
                let mut sum = 0;
                let mut folded = 0;
                let mut new_children = Vec::new();
                for child in node.children() {
                    match child.kind() {
                        NodeKind::Int(i) => {
                            sum -= i;
                            folded += 1;
                        }
                        _ => {
                            new_children.push(child.clone());
                        }
                    }
                }
                if folded > 1 {
                    let sum_node = mngr.const_int(sum);
                    new_children.push(sum_node);
                    Some(mngr.sub(new_children))
                } else {
                    None
                }
            }
            NodeKind::Mul => {
                let mut prod = 1;
                let mut folded = 0;
                let mut new_children = Vec::new();
                for child in node.children() {
                    match child.kind() {
                        NodeKind::Int(i) => {
                            prod *= i;
                            folded += 1;
                        }
                        _ => {
                            new_children.push(child.clone());
                        }
                    }
                }
                if folded > 1 {
                    if prod == 0 {
                        Some(mngr.const_int(0))
                    } else {
                        let prod_node = mngr.const_int(prod);
                        new_children.push(prod_node);
                        Some(mngr.mul(new_children))
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Folds:
/// - R < R  to false
/// - R <= R to true
/// - If if c1, c2 are constant integers:
///   - c1 < c2 to true if c1 < c2
///   - c1 < c2 to false if c1 >= c2
///   - c1 <= c2 to true if c1 <= c2
///   - c1 <= c2 to false if c1 > c2
pub fn int_less_trivial(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Lt {
        // strictly less
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();

        if lhs == rhs {
            return Some(mngr.ffalse());
        }

        match (lhs.kind(), rhs.kind()) {
            (NodeKind::Int(i1), NodeKind::Int(i2)) => {
                if i1 < i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
            }
            _ => (),
        }
    }
    if *node.kind() == NodeKind::Le {
        // less or equal
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();

        if lhs == rhs {
            return Some(mngr.ttrue());
        }

        match (lhs.kind(), rhs.kind()) {
            (NodeKind::Int(i1), NodeKind::Int(i2)) => {
                if i1 <= i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
            }
            _ => (),
        }
    }
    None
}

/// Same as `int_less_trivial`, but for greater than and greater or equal.
pub fn int_greater_trivial(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Gt || *node.kind() == NodeKind::Ge {
        debug_assert!(node.children().len() == 2);

        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();

        // l > r <==> r < l
        // l >= r <==> r <= l

        let swapped_op = if *node.kind() == NodeKind::Gt {
            NodeKind::Lt
        } else {
            NodeKind::Le
        };
        let swapped = mngr.create_node(swapped_op, vec![rhs.clone(), lhs.clone()]);

        return int_less_trivial(&swapped, mngr);
    }

    None
}

pub fn int_equality_trivial(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Eq {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();

        if lhs == rhs {
            return Some(mngr.ttrue());
        }

        match (lhs.kind(), rhs.kind()) {
            (NodeKind::Int(i1), NodeKind::Int(i2)) => {
                if i1 == i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
            }
            _ => (),
        }
    }
    None
}

/// Rewrites len(concat(s1, s2, ..., sn)) to len(s1) + len(s2) + ... + len(sn)
pub fn string_length_addition(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    match node.kind() {
        NodeKind::Length => {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();
            debug_assert!(child.sort().is_string());

            match child.kind() {
                NodeKind::Concat => {
                    let mut terms = Vec::new();
                    for c in child.children() {
                        match c.kind() {
                            NodeKind::String(s) => {
                                terms.push(mngr.const_int(s.len() as i64));
                            }
                            _ => terms.push(mngr.str_len(c.clone())),
                        }
                    }
                    Some(mngr.add(terms))
                }
                NodeKind::String(s) => Some(mngr.const_int(s.len() as i64)),
                NodeKind::Variable(_) => None, // nothing changes
                _ => None,
            }
        }
        _ => None,
    }
}
