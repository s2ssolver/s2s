use std::fmt::Display;

use crate::{ast::NodeKind, context::Sorted};

use super::*;

/// Fold constant integer ter1ms. If i1, i2, ..., in are integer constants, then:
/// - +(i1, i2, ..., in) -> i1 + i2 + ... + in
/// - -(i1, i2, ..., in) -> i1 - i2 - ... - in
/// - *(i1, i2, ..., in) -> i1 * i2 * ... * in
#[derive(Debug, Clone, Copy)]
pub(super) struct FoldConstantInts;
impl EquivalenceRule for FoldConstantInts {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if node.is_const() {
            return None; // already a fully simplified constant
        }

        is_const_int(node).map(|as_i| mngr.const_int(as_i))
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
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::Neg {
            debug_assert!(node.children().len() == 1);
            let child = node.children().first().unwrap();

            if child.kind() == &NodeKind::Add {
                let mut new_children = Vec::new();
                for c in child.children() {
                    new_children.push(mngr.neg(c.clone()));
                }
                return Some(mngr.add(new_children));
            }
        }
        None
    }
}

/// Same as `int_less_trivial`, but for greater than and greater or equal.
#[derive(Debug, Clone, Copy)]
pub(super) struct GreaterTrivial;
impl EquivalenceRule for GreaterTrivial {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
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

            return LessTrivial.apply(&swapped, asserted, mngr);
        }

        None
    }
}

/// Simplifies expressions of the form `x = x` to `true` and `a != a` to `false`, if `a` is a constant integer.
#[derive(Debug, Clone, Copy)]
pub(super) struct EqualityTrivial;
impl EquivalenceRule for EqualityTrivial {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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

/// Normalizes linear (in)-equalities.
/// This rule transforms an (in)-equality into the form `c1*x1 + c2*x2 + ... + cn*xn + c`, where `c1, c2, ..., cn` are the coefficients, `c` is the constant term, and `x1, x2, ..., xn` are atomic integer terms.
#[derive(Debug, Clone, Copy)]
pub(super) struct NormalizeIneq;
impl EquivalenceRule for NormalizeIneq {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if let Some(normed) = normalize_ineq(node) {
            let mut new_children = Vec::new();
            for (k, v) in &normed.lhs.coeffs {
                if *v == 0 {
                    continue;
                }
                let v_node = mngr.const_int(*v);
                if *v == 1 {
                    new_children.push(k.clone());
                } else {
                    let mul = mngr.mul(vec![v_node, k.clone()]);
                    new_children.push(mul);
                }
            }
            let lhs = mngr.add(new_children);
            let rhs = mngr.const_int(normed.rhs);
            let new_node = if normed.pol() {
                mngr.create_node(normed.op, vec![lhs, rhs])
            } else {
                let t = mngr.create_node(normed.op, vec![lhs, rhs]);
                mngr.not(t)
            };
            if new_node == *node {
                None
            } else {
                Some(new_node)
            }
        } else {
            None
        }
    }
}

/// A term describing a linear integer relation.
/// The term is of the form `LHS op RHS`, where `LHS` is a linear term, `op` is a comparison operator, and `RHS` is a constant integer.
/// The polarity of the relation is also stored, which indicates whether the relation is positive or negative.
pub(super) struct LinearIntRealtion {
    lhs: LinTerm,
    op: NodeKind,
    pol: bool,
    rhs: i64,
}

impl Display for LinearIntRealtion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.pol {
            write!(f, "{} {} {}", self.lhs, self.op, self.rhs)
        } else {
            write!(f, "not({} {} {})", self.lhs, self.op, self.rhs)
        }
    }
}

impl LinearIntRealtion {
    fn new(lhs: LinTerm, op: NodeKind, pol: bool, rhs: i64) -> Self {
        LinearIntRealtion { lhs, op, pol, rhs }
    }

    pub fn mult(&mut self, i: i64) {
        if i == 0 {
            self.lhs.coeffs.clear();
            self.lhs.constant = 0;
            self.rhs = 0;
        } else {
            for (_, v) in self.lhs.coeffs.iter_mut() {
                *v = v.checked_mul(i).unwrap();
            }
            self.lhs.constant = self.lhs.constant.checked_mul(i).unwrap();
            self.rhs = self.rhs.checked_mul(i).unwrap();
            if i < 0 {
                self.op = match self.op {
                    NodeKind::Lt => NodeKind::Gt,
                    NodeKind::Le => NodeKind::Ge,
                    NodeKind::Gt => NodeKind::Lt,
                    NodeKind::Ge => NodeKind::Le,
                    NodeKind::Eq => NodeKind::Eq,
                    _ => unreachable!(),
                };
            }
        }
    }

    pub fn flip_polarity(&self) -> Self {
        if self.op == NodeKind::Eq {
            // flip polarity
            LinearIntRealtion {
                lhs: self.lhs.clone(),
                op: self.op.clone(),
                pol: !self.pol,
                rhs: self.rhs,
            }
        } else {
            let new_op = match self.op {
                NodeKind::Lt => NodeKind::Ge,
                NodeKind::Le => NodeKind::Gt,
                NodeKind::Gt => NodeKind::Le,
                NodeKind::Ge => NodeKind::Lt,
                _ => unreachable!(),
            };
            LinearIntRealtion {
                lhs: self.lhs.clone(),
                op: new_op,
                pol: self.pol,
                rhs: self.rhs,
            }
        }
    }

    pub fn lhs(&self) -> &LinTerm {
        &self.lhs
    }

    pub fn rhs(&self) -> i64 {
        self.rhs
    }

    pub fn op(&self) -> &NodeKind {
        &self.op
    }

    pub fn pol(&self) -> bool {
        self.pol
    }
}

pub fn normalize_ineq(node: &Node) -> Option<LinearIntRealtion> {
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
            let mut norm = LinearIntRealtion::new(
                LinTerm {
                    coeffs: new_lhs,
                    constant: 0,
                },
                node.kind().clone(),
                true,
                new_constant,
            );

            // In normal form, we enfore that the first coeffiecient is positive
            if norm
                .lhs()
                .coeffs
                .first()
                .map(|(_, s)| *s < 0)
                .unwrap_or(false)
            {
                norm.mult(-1);
            }

            Some(norm)
        }
        NodeKind::Not => {
            let child = node.children().first().unwrap();
            let normed = normalize_ineq(child)?;
            Some(normed.flip_polarity())
        }
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinTerm {
    /// The coefficients.
    pub coeffs: IndexMap<Node, i64>,
    /// The constant term.
    pub constant: i64,
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
pub fn linearlize_term(node: &Node) -> Option<LinTerm> {
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
pub fn is_const_int(node: &Node) -> Option<i64> {
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
