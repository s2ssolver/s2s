use std::rc::Rc;

use crate::{
    interval::{BoundValue, Interval},
    node::{Node, NodeKind, NodeManager, Sorted, VarSubstitution, Variable},
};

use super::{
    int::{is_const_int, linearlize_term, normalize_ineq},
    EntailmentRule, EquivalenceRule,
};

use indexmap::IndexSet;
use itertools::Itertools;
use smallvec::smallvec;

/// Reduces expressions of the form `len(s)` with `s` a constant string to the length of the string.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConstStringLength;
impl EquivalenceRule for ConstStringLength {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        _: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        if *node.kind() == NodeKind::Length {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            if let NodeKind::String(s) = child.kind() {
                let len = s.len() as i64;
                return Some(mngr.const_int(len));
            }
        }
        None
    }
}

/// Simplifies expressions of the form `len(concat(s1, s2, ..., sn))` to `len(s1) + len(s2) + ... + len(sn)`.
#[derive(Debug, Clone, Copy)]
pub(super) struct StringLengthAddition;
impl EquivalenceRule for StringLengthAddition {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        _: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        if *node.kind() == NodeKind::Length {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            if child.kind() == &NodeKind::Concat {
                let mut sum = Vec::with_capacity(child.children().len());
                for c in child.children() {
                    sum.push(mngr.str_len(c.clone()));
                }
                return Some(mngr.add(sum));
            }
        }
        None
    }
}

/// Fold trivial length constraints.
///
/// - If a linear (in)-equality requires that a string length is less than zero and simplifies it to false if so.
/// - If a string length asserts that the length is greater or equal to zero, it simplifies it to true.
/// - If a string length asserts that the less than or equal to zero, it simplifies it to equal to zero.
#[derive(Debug, Clone, Copy)]
pub(super) struct LengthTrivial;
impl EquivalenceRule for LengthTrivial {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        _: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        match node.kind() {
            NodeKind::Eq | NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => {
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();

                let (ts, kind, mut c) = if let Some(c) = is_const_int(rhs) {
                    let lin = linearlize_term(lhs)?;
                    (lin, node.kind().clone(), c)
                } else if let Some(c) = is_const_int(lhs) {
                    // flip the operator
                    let linearlized = linearlize_term(rhs)?;
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
                        NodeKind::Le if c == 0 && coeffs_positive => {
                            let lhs_new = ts
                                .coeffs
                                .iter()
                                .map(|(n, v)| (n, mngr.const_int(*v)))
                                .collect_vec()
                                .into_iter()
                                .map(|(n, v)| mngr.mul(vec![v, n.clone()]))
                                .collect();
                            let lhs_new = mngr.add(lhs_new);
                            let rhs_new = mngr.const_int(0);
                            let new_eq = mngr.eq(lhs_new, rhs_new);
                            return Some(new_eq);
                        }
                        NodeKind::Gt if c < 0 && coeffs_positive => {
                            return Some(mngr.ttrue());
                        }
                        NodeKind::Ge if c <= 0 && coeffs_positive => {
                            return Some(mngr.ttrue());
                        }
                        NodeKind::Ge if c == 0 && coeffs_positive => {
                            // This is a trivial constraint, we can remove it
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
    fn apply(
        &self,
        node: &Node,
        _: bool,
        _: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        let normed = normalize_ineq(node)?;
        if normed.lhs().coeffs.len() == 1 {
            // This is a constraint of the form `s|x| # rhs`, we can rewrite this as a regular constraint
            let (x, s) = normed.lhs().coeffs.iter().next().unwrap();

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

            let c = normed.rhs();
            let op = normed.op().clone();
            let (r, op, s) = match (c >= 0, *s >= 0) {
                (true, true) => (c as u32, op, *s as u32), // both positive
                (false, false) if op != NodeKind::Eq => match op {
                    NodeKind::Lt => (-c as u32, NodeKind::Gt, -*s as u32),
                    NodeKind::Le => (-c as u32, NodeKind::Ge, -*s as u32),
                    NodeKind::Gt => (-c as u32, NodeKind::Lt, -*s as u32),
                    NodeKind::Ge => (-c as u32, NodeKind::Le, -*s as u32),
                    NodeKind::Eq if normed.pol() => (-c as u32, NodeKind::Eq, -*s as u32),
                    _ => return None,
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

        None
    }
}

/// Finds asserted terms of the form `L = 0` or `L <= 0`, where
/// all terms in L are of the form c|x| with c>0
/// and returns `x = epsilon` for all c|x| in L.`
#[derive(Clone, Default, Debug)]
pub(super) struct ZeroLengthEpsilon;

impl ZeroLengthEpsilon {
    fn apply(lhs: &Node, mngr: &mut NodeManager) -> Option<VarSubstitution> {
        // Collects all in the given node of sort string that need to be replaced by epsilon
        // Returns false if a variable is found that is not of sort string
        fn collect_vars(n: &Node, in_len: bool, vars: &mut IndexSet<Rc<Variable>>) -> bool {
            match n.kind() {
                NodeKind::Length => {
                    assert!(!in_len);
                    for c in n.children() {
                        // must be true since the length of a string is a string
                        collect_vars(c, true, vars);
                    }
                    true
                }
                NodeKind::Concat => {
                    assert!(in_len);
                    for c in n.children() {
                        // must be true since we can only concatenate strings
                        collect_vars(c, in_len, vars);
                    }
                    true
                }
                NodeKind::Variable(v) if in_len => {
                    // must be a string, we are in a length
                    assert!(v.sort().is_string());
                    vars.insert(v.clone());
                    true
                }
                NodeKind::Mul | NodeKind::Add => {
                    assert!(!in_len);
                    for c in n.children() {
                        if !collect_vars(c, in_len, vars) {
                            // If we find a variable that is not of sort string, we can't apply the rule
                            // and return false
                            return false;
                        }
                    }
                    true
                }
                NodeKind::Int(i) => *i >= 0, // if we find a negative integer, we can't apply the rule
                NodeKind::Sub => false,
                NodeKind::Variable(v) => {
                    debug_assert!(!in_len);
                    debug_assert!(v.sort().is_int());
                    // if we find a variable that is not of sort string, we can't apply the rule
                    false
                }
                _ => false,
            }
        }
        let mut vars = IndexSet::new();
        if collect_vars(lhs, false, &mut vars) && !vars.is_empty() {
            // set all variables to epsilon
            let mut subs = VarSubstitution::default();
            let epsi = mngr.empty_string();
            for v in vars {
                subs.add(v, epsi.clone());
            }
            Some(subs)
        } else {
            None
        }
    }
}

impl EntailmentRule for ZeroLengthEpsilon {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        _: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution> {
        // This is only applicable if the node itself is asserted
        if !asserted.contains(node) {
            return None;
        }

        match node.kind() {
            NodeKind::Eq => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if lhs.sort().is_int() && rhs.sort().is_int() {
                    match (lhs.kind(), rhs.kind()) {
                        (_, NodeKind::Int(0)) => return ZeroLengthEpsilon::apply(lhs, mngr),
                        (NodeKind::Int(0), _) => return ZeroLengthEpsilon::apply(rhs, mngr),
                        _ => (),
                    }
                }
            }
            NodeKind::Le => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if let (NodeKind::Int(0), _) = (lhs.kind(), rhs.kind()) {
                    return ZeroLengthEpsilon::apply(lhs, mngr);
                }
            }
            NodeKind::Ge => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                if let (NodeKind::Int(0), _) = (lhs.kind(), rhs.kind()) {
                    return ZeroLengthEpsilon::apply(rhs, mngr);
                }
            }
            _ => (),
        }
        None
    }
}

/// Finds asserted terms of the form `L # c` where L is a linear combination of string lengths
/// and c is a constant integer.
/// Returns `false` if `c` is not in the range of possible value `L` can take.
#[derive(Clone, Default, Debug)]
pub(super) struct TrivialLenghtConstraints;

impl EquivalenceRule for TrivialLenghtConstraints {
    fn apply(
        &self,
        node: &Node,
        _: bool,
        _: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        let normed = normalize_ineq(node)?;

        let all_str_len = normed
            .lhs()
            .coeffs
            .iter()
            .all(|(n, _)| matches!(n.kind(), NodeKind::Length));

        if all_str_len {
            // Compute the range of possible values for L, which is
            // - [0, +inf] if all coefficients are positive
            // - [-inf, 0] if all coefficients are negative
            // - [0, 0] if all coefficients are zero
            // - [-int, +inf] if some coefficients are positive and some are negative

            let coeffs = normed
                .lhs()
                .coeffs
                .iter()
                .map(|(_, v)| *v)
                .collect::<Vec<_>>();
            let all_positive = coeffs.iter().all(|v| *v > 0);
            let all_negative = coeffs.iter().all(|v| *v < 0);
            let all_zero = coeffs.iter().all(|v| *v == 0);
            let range = match (all_positive, all_negative, all_zero) {
                (true, false, false) => Interval::bounded_below(0),
                (false, true, false) => Interval::bounded_above(0),
                (false, false, true) => Interval::new(0, 0),
                (false, false, false) => Interval::unbounded(),
                _ => unreachable!(),
            };

            // check if we can cast to i32
            if normed.rhs() > i32::MAX as i64 || normed.rhs() < i32::MIN as i64 {
                return None;
            }

            let c = BoundValue::Num(normed.rhs() as i32);
            match normed.op() {
                NodeKind::Lt if normed.pol() => {
                    if c <= range.lower() {
                        return Some(mngr.ffalse());
                    }
                }
                NodeKind::Le if normed.pol() => {
                    if c < range.lower() {
                        return Some(mngr.ffalse());
                    }
                }
                NodeKind::Eq if normed.pol() => {
                    if c < range.lower() || c > range.upper() {
                        return Some(mngr.ffalse());
                    }
                }
                NodeKind::Ge if normed.pol() => {
                    if c > range.upper() {
                        return Some(mngr.ffalse());
                    }
                }
                NodeKind::Gt if normed.pol() => {
                    if c >= range.upper() {
                        return Some(mngr.ffalse());
                    }
                }
                _ => return None,
            }
        }
        None
    }
}
