use std::rc::Rc;

use indexmap::IndexSet;

use crate::node::{NodeKind, Sorted, Variable};

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

/// Distributes negation over the children of a node.
/// - `-(a + b) -> -a + -b``
pub fn distribute_neg(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Neg {
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();

        match child.kind() {
            NodeKind::Add => {
                let mut new_children = Vec::new();
                for c in child.children() {
                    new_children.push(mngr.neg(c.clone()));
                }
                Some(mngr.add(new_children))
            }
            _ => None,
        }
    } else {
        None
    }
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

/// Reduces expressions of the form `len(s)` with `s` a constant string to the length of the string.
pub fn const_string_length(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Length {
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();

        match child.kind() {
            NodeKind::String(s) => {
                let len = s.chars().count() as i64;
                Some(mngr.const_int(len))
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Simplifies expressions of the form `len(concat(s1, s2, ..., sn))` to `len(s1) + len(s2) + ... + len(sn)`.
pub fn string_length_addition(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Length {
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();

        match child.kind() {
            NodeKind::Concat => {
                let mut sum = Vec::with_capacity(child.children().len());
                for c in child.children() {
                    sum.push(mngr.str_len(c.clone()));
                }
                Some(mngr.add(sum))
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Checks if a linear (in)-equality requires that a string length is less than zero and simplifies it to false if so.
pub fn length_positive(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    /// If the term is a sum of positively scaled string lengths, return the set of variables.
    /// Otherwise, returns None
    fn all_pos_len(node: &Node) -> Option<IndexSet<Rc<Variable>>> {
        match node.kind() {
            NodeKind::Mul if node.children().len() == 2 => {
                let (lhs, rhs) = (
                    node.children().first().unwrap(),
                    node.children().last().unwrap(),
                );
                match (lhs.kind(), rhs.kind()) {
                    (NodeKind::Int(i), NodeKind::Length) if *i > 0 => {
                        if let NodeKind::Variable(v) = rhs.kind() {
                            let mut vars = IndexSet::new();
                            vars.insert(v.clone());
                            Some(vars)
                        } else {
                            None
                        }
                    }
                    (NodeKind::Length, NodeKind::Int(i)) if *i > 0 => {
                        if let NodeKind::Variable(v) = lhs.kind() {
                            let mut vars = IndexSet::new();
                            vars.insert(v.clone());
                            Some(vars)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            NodeKind::Add => {
                let mut vars = IndexSet::new();
                for c in node.children() {
                    if let NodeKind::Mul = c.kind() {
                        vars.extend(all_pos_len(c)?)
                    } else {
                        return None;
                    }
                }
                Some(vars)
            }
            NodeKind::Length => {
                if let NodeKind::Variable(v) = node.children().first().unwrap().kind() {
                    let mut vars = IndexSet::new();
                    vars.insert(v.clone());
                    Some(vars)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    match node.kind() {
        NodeKind::Eq => {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if lhs.sort().is_int() && rhs.sort().is_int() {
                match (lhs.kind(), rhs.kind()) {
                    (_, NodeKind::Int(i)) if *i < 0 => {
                        if all_pos_len(lhs).is_some() {
                            return Some(mngr.ffalse());
                        }
                    }
                    (NodeKind::Int(i), _) if *i < 0 => {
                        if all_pos_len(rhs).is_some() {
                            return Some(mngr.ffalse());
                        }
                    }
                    _ => (),
                }
            }
        }
        NodeKind::Lt => {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if let NodeKind::Int(i) = rhs.kind() {
                if *i <= 0 {
                    if all_pos_len(lhs).is_some() {
                        return Some(mngr.ffalse());
                    }
                }
            }
        }
        NodeKind::Le => {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if let NodeKind::Int(i) = rhs.kind() {
                if *i < 0 {
                    if all_pos_len(lhs).is_some() {
                        return Some(mngr.ffalse());
                    }
                }
            }
        }
        NodeKind::Gt => {
            // 0 > lengths
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if let NodeKind::Int(i) = lhs.kind() {
                if 0 >= *i {
                    if all_pos_len(rhs).is_some() {
                        return Some(mngr.ffalse());
                    }
                }
            }
        }
        NodeKind::Ge => {
            // -1 >= lengths
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            if let NodeKind::Int(i) = lhs.kind() {
                if 0 > *i {
                    if all_pos_len(rhs).is_some() {
                        return Some(mngr.ffalse());
                    }
                }
            }
        }
        _ => (),
    }
    return None;
}
