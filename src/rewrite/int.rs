use crate::node::{NodeKind, Sorted};

use super::*;

pub struct FoldConstantInts;

impl RewriteRule for FoldConstantInts {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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
        } else if node.sort().is_bool() {
            // Try reduce constant relations
            if node.children().len() == 2 {
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if let (NodeKind::Int(i1), NodeKind::Int(i2)) = (lhs.kind(), rhs.kind()) {
                    match node.kind() {
                        NodeKind::Eq => {
                            if i1 == i2 {
                                Some(mngr.ttrue())
                            } else {
                                Some(mngr.ffalse())
                            }
                        }
                        NodeKind::Le => {
                            if i1 <= i2 {
                                Some(mngr.ttrue())
                            } else {
                                Some(mngr.ffalse())
                            }
                        }
                        NodeKind::Lt => {
                            if i1 < i2 {
                                Some(mngr.ttrue())
                            } else {
                                Some(mngr.ffalse())
                            }
                        }
                        NodeKind::Ge => {
                            if i1 >= i2 {
                                Some(mngr.ttrue())
                            } else {
                                Some(mngr.ffalse())
                            }
                        }
                        NodeKind::Gt => {
                            if i1 > i2 {
                                Some(mngr.ttrue())
                            } else {
                                Some(mngr.ffalse())
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

pub struct LengthOfConcatToAddition;

impl RewriteRule for LengthOfConcatToAddition {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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
}
