use crate::node::{Node, NodeKind, NodeManager};

use super::{
    int::{is_const_int, linearlize_term, normalize_ineq},
    EquivalenceRule,
};

use indexmap::IndexSet;
use smallvec::smallvec;

/// Reduces expressions of the form `len(s)` with `s` a constant string to the length of the string.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConstStringLength;
impl EquivalenceRule for ConstStringLength {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Length {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            match child.kind() {
                NodeKind::String(s) => {
                    let len = s.len() as i64;
                    return Some(mngr.const_int(len));
                }
                _ => (),
            }
        }
        None
    }
}

/// Simplifies expressions of the form `len(concat(s1, s2, ..., sn))` to `len(s1) + len(s2) + ... + len(sn)`.
#[derive(Debug, Clone, Copy)]
pub(super) struct StringLengthAddition;
impl EquivalenceRule for StringLengthAddition {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Length {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            match child.kind() {
                NodeKind::Concat => {
                    let mut sum = Vec::with_capacity(child.children().len());
                    for c in child.children() {
                        sum.push(mngr.str_len(c.clone()));
                    }
                    return Some(mngr.add(sum));
                }
                _ => (),
            }
        }
        None
    }
}

/// Checks if a linear (in)-equality requires that a string length is less than zero and simplifies it to false if so.
#[derive(Debug, Clone, Copy)]
pub(super) struct LengthTrivial;
impl EquivalenceRule for LengthTrivial {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        match node.kind() {
            NodeKind::Eq | NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => {
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();

                let (ts, kind, mut c) = if let Some(c) = is_const_int(rhs) {
                    let lin = match linearlize_term(lhs) {
                        Some(l) => l,
                        None => return None,
                    };
                    (lin, node.kind().clone(), c)
                } else if let Some(c) = is_const_int(lhs) {
                    // flip the operator
                    let linearlized = match linearlize_term(rhs) {
                        Some(l) => l,
                        None => return None,
                    };
                    match node.kind() {
                        NodeKind::Lt => (linearlized, NodeKind::Gt, c),
                        NodeKind::Le => (linearlized, NodeKind::Ge, c),
                        NodeKind::Gt => (linearlized, NodeKind::Lt, c),
                        NodeKind::Ge => (linearlized, NodeKind::Le, c),
                        _ => return None,
                    }
                } else {
                    return None;
                };

                c -= ts.constant;

                if ts.coeffs.iter().all(|(n, _)| *n.kind() == NodeKind::Length) {
                    // all coefficients are positive
                    let coeffs_positive = ts.coeffs.iter().all(|(_, v)| *v >= 0);

                    match kind {
                        NodeKind::Eq if ts.coeffs.len() == 1 && c == 0 => {
                            // that string term needs to be epsilon
                            let (var, _) = ts.coeffs.iter().next().unwrap();
                            debug_assert!(*var.kind() == NodeKind::Length);
                            let ch = var.children().first().unwrap();
                            let epsi = mngr.empty_string();
                            return Some(mngr.eq(ch.clone(), epsi));
                        }
                        NodeKind::Eq if c < 0 && coeffs_positive => {
                            return Some(mngr.ffalse());
                        }
                        NodeKind::Lt if c <= 0 && coeffs_positive => {
                            return Some(mngr.ffalse());
                        }
                        NodeKind::Le if c < 0 && coeffs_positive => {
                            return Some(mngr.ffalse());
                        }
                        NodeKind::Gt if c < 0 && coeffs_positive => {
                            return Some(mngr.ttrue());
                        }
                        NodeKind::Ge if c <= 0 && coeffs_positive => {
                            return Some(mngr.ttrue());
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        }
        None
    }
}

/// Converts lineaer constraints of the form `s|x| # rhs` to regular constraints.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub(super) struct LengthToReg;
impl EquivalenceRule for LengthToReg {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if let Some((lhs, op, c)) = normalize_ineq(node) {
            if lhs.coeffs.len() == 1 {
                // This is a constraint of the form `s|x| # rhs`, we can rewrite this as a regular constraint
                let (x, s) = lhs.coeffs.iter().next().unwrap();

                // Only works if we have an lhs of the for str.len(x) or str.len(x) * s where x is a variable
                let x = if x.kind() == &NodeKind::Length {
                    let ch = x.children().first().unwrap();
                    if !matches!(ch.kind(), NodeKind::Variable(_)) {
                        return None;
                    }
                    ch.clone()
                } else {
                    return None;
                };

                let (r, op, s) = match (c >= 0, *s >= 0) {
                    (true, true) => (c as u32, op, *s as u32), // both positive
                    (false, false) if op != NodeKind::Eq => match op {
                        NodeKind::Lt => (-c as u32, NodeKind::Gt, -*s as u32),
                        NodeKind::Le => (-c as u32, NodeKind::Ge, -*s as u32),
                        NodeKind::Gt => (-c as u32, NodeKind::Lt, -*s as u32),
                        NodeKind::Ge => (-c as u32, NodeKind::Le, -*s as u32),
                        NodeKind::Eq => (-c as u32, NodeKind::Eq, -*s as u32),
                        _ => unreachable!(),
                    },
                    _ => return None,
                };

                let builder = mngr.re_builder();
                let re = match op {
                    NodeKind::Lt => {
                        let u = r / s;
                        if r % s == 0 {
                            builder.loop_(builder.allchar(), 0, u - 1)
                        } else {
                            builder.loop_(builder.allchar(), 0, u)
                        }
                    }
                    NodeKind::Le => {
                        let u = r / s;
                        builder.loop_(builder.allchar(), 0, u)
                    }
                    NodeKind::Gt => {
                        let l = r.div_ceil(s);
                        let lower = builder.pow(builder.allchar(), l + 1);
                        builder.concat(smallvec![lower, builder.all()])
                    }
                    NodeKind::Ge => {
                        let l = r.div_ceil(s);
                        let lower = builder.pow(builder.allchar(), l);
                        builder.concat(smallvec![lower, builder.all()])
                    }
                    NodeKind::Eq => {
                        if r % s == 0 {
                            builder.pow(builder.allchar(), r / s)
                        } else {
                            builder.none()
                        }
                    }
                    _ => unreachable!(),
                };
                let re = mngr.const_regex(re);
                let inre = mngr.in_re(x.clone(), re);
                return Some(inre);
            }
        }
        None
    }
}
