use std::{collections::HashSet, fmt::Display, rc::Rc};

use crate::node::{NodeKind, Sorted, Variable};

use super::*;

/// Fold constant integer terms. If i1, i2, ..., in are integer constants, then:
/// - +(i1, i2, ..., in) -> i1 + i2 + ... + in
/// - -(i1, i2, ..., in) -> i1 - i2 - ... - in
/// - *(i1, i2, ..., in) -> i1 * i2 * ... * in
#[derive(Debug, Clone, Copy)]
pub(super) struct FoldConstantInts;
impl EquivalenceRule for FoldConstantInts {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if node.is_const() {
            return None; // already a fully simplified constant
        }

        match is_const_int(node) {
            Some(as_i) => Some(mngr.const_int(as_i)),
            None => None,
        }
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
#[derive(Debug, Clone, Copy)]
pub(super) struct LessTrivial;
impl EquivalenceRule for LessTrivial {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Lt {
            // strictly less
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();

            if lhs == rhs {
                return Some(mngr.ffalse());
            }

            if let (NodeKind::Int(i1), NodeKind::Int(i2)) = (lhs.kind(), rhs.kind()) {
                if i1 < i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
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

            if let (NodeKind::Int(i1), NodeKind::Int(i2)) = (lhs.kind(), rhs.kind()) {
                if i1 <= i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
            }
        }
        None
    }
}

/// Distributes negation over the children of a node.
/// - `-(a + b) -> -a + -b``
#[derive(Debug, Clone, Copy)]
pub(super) struct DistributeNeg;
impl EquivalenceRule for DistributeNeg {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Neg {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            match child.kind() {
                NodeKind::Add => {
                    let mut new_children = Vec::new();
                    for c in child.children() {
                        new_children.push(mngr.neg(c.clone()));
                    }
                    return Some(mngr.add(new_children));
                }
                _ => (),
            }
        }
        None
    }
}

/// Same as `int_less_trivial`, but for greater than and greater or equal.
#[derive(Debug, Clone, Copy)]
pub(super) struct GreaterTrivial;
impl EquivalenceRule for GreaterTrivial {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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

            return LessTrivial.apply(&swapped, mngr);
        }

        None
    }
}

/// Simplifies expressions of the form `x = x` to `true` and `a != a` to `false`, if `a` is a constant integer.
#[derive(Debug, Clone, Copy)]
pub(super) struct EqualityTrivial;
impl EquivalenceRule for EqualityTrivial {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Eq {
            debug_assert!(node.children().len() == 2);
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();

            if lhs == rhs {
                return Some(mngr.ttrue());
            }

            if let (NodeKind::Int(i1), NodeKind::Int(i2)) = (lhs.kind(), rhs.kind()) {
                if i1 == i2 {
                    return Some(mngr.ttrue());
                } else {
                    return Some(mngr.ffalse());
                }
            }
        }
        None
    }
}

/// Simplifies expressions of the form `not(t1 # t2)` where `#` is a comparison operator.
///
/// - `not(t1 < t2)` -> `t1 >= t2`
/// - `not(t1 <= t2)` -> `t1 > t2`
/// - `not(t1 > t2)` -> `t1 <= t2`
/// - `not(t1 >= t2)` -> `t1 < t2`
#[derive(Debug, Clone, Copy)]
pub(super) struct NotComparison;
impl EquivalenceRule for NotComparison {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if let NodeKind::Not = *node.kind() {
            let child = node.children().first().unwrap();
            match child.kind() {
                NodeKind::Lt => {
                    return Some(mngr.create_node(NodeKind::Ge, child.children().to_vec()))
                }
                NodeKind::Le => {
                    return Some(mngr.create_node(NodeKind::Gt, child.children().to_vec()))
                }
                NodeKind::Gt => {
                    return Some(mngr.create_node(NodeKind::Le, child.children().to_vec()))
                }
                NodeKind::Ge => {
                    return Some(mngr.create_node(NodeKind::Lt, child.children().to_vec()))
                }
                _ => (),
            }
        }
        None
    }
}

/// Reduces expressions of the form `len(s)` with `s` a constant string to the length of the string.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConstStringLength;
impl EquivalenceRule for ConstStringLength {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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

/// Normalizes linear (in)-equalities.
/// This rule transforms an (in)-equality into the form `c1*x1 + c2*x2 + ... + cn*xn + c`, where `c1, c2, ..., cn` are the coefficients, `c` is the constant term, and `x1, x2, ..., xn` are atomic integer terms.
#[derive(Debug, Clone, Copy)]
pub(super) struct NormalizeIneq;
impl EquivalenceRule for NormalizeIneq {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if let Some(new_node) = normalize_ineq(node, mngr) {
            Some(new_node)
        } else {
            None
        }
    }
}
fn normalize_ineq(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    match node.kind() {
        NodeKind::Eq | NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge
            if node.children()[0].sort().is_int() && node.children()[1].sort().is_int() =>
        {
            let lin_lhs = linearlize_term(&node.children()[0])?;
            let lin_rhs = linearlize_term(&node.children()[1])?;

            // move all terms to the left
            let mut new_lhs = IndexMap::new();
            for (k, v) in lin_lhs.coeffs {
                *new_lhs.entry(k).or_insert(0) += v;
            }
            for (k, v) in lin_rhs.coeffs {
                *new_lhs.entry(k).or_insert(0) -= v;
            }
            let new_constant = lin_rhs.constant - lin_lhs.constant;

            let mut new_children = Vec::new();
            for (k, v) in new_lhs {
                if v == 0 {
                    continue;
                }
                let v_node = mngr.const_int(v);
                if v == 1 {
                    new_children.push(k);
                } else {
                    let mul = mngr.mul(vec![v_node, k.clone()]);
                    new_children.push(mul);
                }
            }
            let lhs = mngr.add(new_children);
            let rhs = mngr.const_int(new_constant);
            let new_node = mngr.create_node(node.kind().clone(), vec![lhs, rhs]);
            if new_node == *node {
                None
            } else {
                Some(new_node)
            }
        }
        _ => None,
    }
}

struct LinTerm {
    /// The coefficients.
    coeffs: IndexMap<Node, i64>,
    /// The constant term.
    constant: i64,
}

impl Display for LinTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (k, v) in self.coeffs.iter() {
            if !first {
                write!(f, " + ")?;
            }
            first = false;
            if *v != 1 {
                write!(f, "{}*", v)?;
            }
            write!(f, "{}", k)?;
        }
        if !first {
            write!(f, " + ")?;
        }
        write!(f, "{}", self.constant)
    }
}

/// Transforms a linear (in)-equality into normal form.
/// In normal form, the term has the form `c1*x1 + c2*x2 + ... + cn*xn + c`, where `c1, c2, ..., cn` are the coefficients, `c` is the constant term, and `x1, x2, ..., xn` are atomic integer terms.
fn linearlize_term(node: &Node) -> Option<LinTerm> {
    let mut coeffs = IndexMap::new();
    let mut constant = 0;
    match node.kind() {
        NodeKind::Add => {
            for c in node.children() {
                let lt = linearlize_term(c)?;
                for (k, v) in lt.coeffs {
                    *coeffs.entry(k).or_insert(0) += v;
                }
                constant += lt.constant;
            }
        }
        NodeKind::Sub => {
            let mut iter = node.children().iter();
            let first = linearlize_term(iter.next().unwrap())?;
            for (k, v) in first.coeffs {
                *coeffs.entry(k).or_insert(0) += v;
            }
            constant += first.constant;
            for c in iter {
                let lt = linearlize_term(c)?;
                for (k, v) in lt.coeffs {
                    *coeffs.entry(k).or_insert(0) -= v;
                }
                constant -= lt.constant;
            }
        }
        NodeKind::Neg => {
            let lt = linearlize_term(node.children().first().unwrap())?;
            for (k, v) in lt.coeffs {
                *coeffs.entry(k).or_insert(0) -= v;
            }
            constant -= lt.constant;
        }
        NodeKind::Mul => {
            let mut iter = node.children().iter();
            let mut left = linearlize_term(iter.next().unwrap())?;
            for c in iter {
                let right = linearlize_term(c)?;
                match (&left.coeffs.is_empty(), right.coeffs.is_empty()) {
                    (true, true) => {
                        left.constant *= right.constant;
                    }
                    (true, false) => {
                        let c = left.constant;
                        left = right;
                        // distribute the constant
                        left.constant *= c;
                        for (_, v) in left.coeffs.iter_mut() {
                            *v *= c
                        }
                    }
                    (false, true) => {
                        let c = right.constant;
                        // distribute the constant
                        for (_, v) in left.coeffs.iter_mut() {
                            *v *= c;
                        }
                        left.constant *= c;
                    }
                    (false, false) => {
                        return None;
                    }
                }
            }
            coeffs = left.coeffs;
            constant = left.constant;
        }
        _ if node.sort().is_int() => {
            if let Some(i) = is_const_int(node) {
                constant = i;
            } else {
                *coeffs.entry(node.clone()).or_insert(0) += 1;
            }
        }
        _ => return None,
    }
    Some(LinTerm { coeffs, constant })
}

/// Return the constant integer value of a node if it is a constant integer.
/// Otherwise, return None.
fn is_const_int(node: &Node) -> Option<i64> {
    match node.kind() {
        NodeKind::Int(i) => Some(*i),
        NodeKind::Neg => {
            let i = is_const_int(node.children().first().unwrap())?;
            Some(-i)
        }
        NodeKind::Add => {
            let mut sum = 0;
            for c in node.children() {
                sum += is_const_int(c)?;
            }
            Some(sum)
        }
        NodeKind::Mul => {
            let mut prod = 1;
            let mut is_const = true;

            for c in node.children() {
                match is_const_int(c) {
                    Some(0) => return Some(0),
                    Some(c) => prod *= c,
                    None => {
                        is_const = false;
                    }
                }
            }

            if is_const {
                Some(prod)
            } else {
                None
            }
        }
        NodeKind::Sub => {
            let mut iter = node.children().iter();
            let first = is_const_int(iter.next().unwrap())?;
            let mut sub_sum = 0;
            for c in iter {
                let next = is_const_int(c)?;
                sub_sum += next;
            }
            Some(first - sub_sum)
        }
        NodeKind::Length => {
            let child = node.children().first().unwrap();
            match child.kind() {
                NodeKind::String(s) => Some(s.len() as i64),
                _ => None,
            }
        }
        _ => None,
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
        fn collect_vars(n: &Node, in_len: bool, vars: &mut HashSet<Rc<Variable>>) -> bool {
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
        let mut vars = HashSet::new();
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
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<VarSubstitution> {
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
                match (lhs.kind(), rhs.kind()) {
                    (_, NodeKind::Int(0)) => return ZeroLengthEpsilon::apply(lhs, mngr),
                    _ => (),
                }
            }
            NodeKind::Ge => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap();
                let rhs = node.children().last().unwrap();
                match (lhs.kind(), rhs.kind()) {
                    (NodeKind::Int(0), _) => return ZeroLengthEpsilon::apply(rhs, mngr),
                    _ => (),
                }
            }
            _ => (),
        }
        None
    }
}
