//! Conversion of nodes into canonical form.

mod int;
mod string;

pub use int::LinearConstraint;
use int::{LinearArithTerm, LinearOperator};
use string::Pattern;
pub use string::{FactorConstraint, FactorConstraintType, RegularConstraint, WordEquation};
use utils::SymbolIterator;

use super::*;
use error::NodeError;
use indexmap::IndexMap;

use std::collections::HashMap;

pub fn canonicalize(node: Node, mngr: &mut NodeManager) -> Result<Node, NodeError> {
    let mut canonicalizer = Canonicalizer::default();
    canonicalizer.canonicalize(node, mngr)
}

#[derive(Default)]
struct Canonicalizer {
    /// Identities of the form t = v, where t is a term and v is a variable.
    /// Theses dentities are introduced during the canonicalization process if a term is not in canonical form.
    def_identities: HashMap<Node, Rc<Variable>>,
    mapper: CanonicalMapper,
}

impl Canonicalizer {
    /// Brings all literals into canonical form.
    fn canonicalize(&mut self, node: Node, mngr: &mut NodeManager) -> Result<Node, NodeError> {
        if node.is_literal() {
            if let NodeKind::Not = node.kind() {
                debug_assert!(node.children().len() == 1);
                let child = node.children().first().unwrap();
                return self.canonicalize_lit(child.clone(), false, mngr);
            } else {
                return self.canonicalize_lit(node, true, mngr);
            }
        } else if node.is_bool_fun() {
            match node.kind() {
                NodeKind::And | NodeKind::Or => {
                    let rec = node
                        .children()
                        .into_iter()
                        .map(|c| self.canonicalize(c.clone(), mngr))
                        .collect::<Result<Vec<Node>, _>>();
                    return Ok(mngr.create_node(node.kind().clone(), rec?));
                }
                NodeKind::Not | NodeKind::Imp | NodeKind::Equiv => {
                    return Err(NodeError::NotInNegationNormalForm(node))
                }
                _ => unreachable!("Expected boolean function"),
            }
        } else {
            // The node is a term, this should not happen in a well-formed formula.
            return Err(NodeError::NotWellFormed(node));
        }
    }

    fn canonicalize_lit(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.is_literal());

        let canonicalized = match node.kind() {
            NodeKind::Variable(v) => {
                debug_assert!(v.sort().is_bool());
                Ok(node)
            }
            NodeKind::Bool(_) => Ok(node),
            NodeKind::InRe => self.canonicalize_in_re(node, pol, mngr),
            NodeKind::Contains => self.canonicalize_contains(node, pol, mngr),
            NodeKind::PrefixOf => self.canonicalize_prefixof(node, pol, mngr),
            NodeKind::SuffixOf => self.canonicalize_suffixof(node, pol, mngr),
            NodeKind::Eq => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap().sort();
                let rhs = node.children().last().unwrap().sort();
                if lhs == rhs {
                    if lhs.is_string() {
                        self.canonicalize_weq(node, pol, mngr)
                    } else if lhs.is_int() {
                        self.canonicalize_arithmetic_constraint(node, pol, mngr)
                    } else {
                        Err(NodeError::NotWellFormed(node))
                    }
                } else {
                    Err(NodeError::SortMismatch(node, lhs, rhs))
                }
            }
            NodeKind::Gt | NodeKind::Ge | NodeKind::Lt | NodeKind::Le => {
                self.canonicalize_arithmetic_constraint(node, pol, mngr)
            }
            _ => unreachable!("Expected atomic formula but got '{}'", node),
        }?;
        if let Some(canonical) = self.mapper.lit2ir(&canonicalized) {
            canonicalized.set_canonical(canonical);
        }
        Ok(canonicalized)
    }

    fn canonicalize_in_re(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(*node.kind() == NodeKind::InRe);
        debug_assert!(node.children().len() == 2);

        let pat = node.children().first().unwrap();
        if pat.is_var() || pat.is_const() {
            return Ok(node);
        }
        let v = self.define_with_var(pat, mngr);
        let inre = mngr.in_re(v, node.children().last().unwrap().clone());
        if pol {
            return Ok(inre);
        } else {
            return Ok(mngr.not(inre));
        }
    }

    fn canonicalize_prefixof(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(*node.kind() == NodeKind::PrefixOf);
        // PrefixOf(r, s) <--> EX t. r = s ++ t
        // If the polarity is negative, this introduces a universal quantifier, which cannot be handled.
        // In that case, the node is kept as is.
        if pol {
            let r = node.children().first().unwrap();
            let s = node.children().last().unwrap();
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![s.clone(), t.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            Ok(eq)
        } else {
            Ok(node)
        }
    }

    fn canonicalize_suffixof(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(*node.kind() == NodeKind::SuffixOf);
        // SuffixOf(r, s) <--> EX t. r = t ++ s
        // If the polarity is negative, this introduces a universal quantifier, which cannot be handled.
        // In that case, the node is kept as is.
        if pol {
            let r = node.children().first().unwrap();
            let s = node.children().last().unwrap();
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![t.clone(), s.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            Ok(eq)
        } else {
            Ok(node)
        }
    }

    fn canonicalize_contains(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(*node.kind() == NodeKind::Contains);
        // Contains(r, s) <--> EX t, u. r = t ++ s ++ u
        // If the polarity is negative, this introduces a universal quantifier, which cannot be handled.
        // In that case, the node is kept as is.
        if pol {
            let r = node.children().first().unwrap();
            let s = node.children().last().unwrap();
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let u = mngr.temp_var(Sort::String);
            let u = mngr.var(u);
            let rhs = mngr.concat(vec![t.clone(), s.clone(), u.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            Ok(eq)
        } else {
            Ok(node)
        }
    }

    fn canonicalize_weq(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(*node.kind() == NodeKind::Eq);
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_string());
        debug_assert!(rhs.sort().is_string());
        let lhs = self.canonicalize_concat(lhs.clone(), mngr);
        let rhs = self.canonicalize_concat(rhs.clone(), mngr);
        let eq = mngr.eq(lhs, rhs);
        if pol {
            Ok(eq)
        } else {
            Ok(mngr.not(eq))
        }
    }

    /// Canocalizes nodes of the form (concat t1 ... tn). The result is a new node (concat r1 ... rm)
    /// where each ri is a einther a (string) variable or a constant. Does the following:
    /// - If any of node ti is not a variable or a constant, ti is replaced by a new variable ri and the identity ti = ri is stored.
    /// - If ti is a concatenation, it is recursively canonicalized and flattened.
    fn canonicalize_concat(&mut self, node: Node, mngr: &mut NodeManager) -> Node {
        debug_assert!(
            *node.kind() == NodeKind::Concat || node.is_var() || node.is_const(),
            "Expected concatenation, variable, or constant but got '{}'",
            node
        );
        if node.is_var() || node.is_const() {
            return node;
        }
        let mut rec: Vec<Node> = Vec::with_capacity(node.children().len());
        for c in node.children() {
            match c.kind() {
                NodeKind::Variable(_) | NodeKind::String(_) => rec.push(c.clone()),
                NodeKind::Concat => {
                    // recursively canonicalize the sub-concatenation and flatten the result
                    let canonical = self.canonicalize_concat(c.clone(), mngr);
                    rec.extend(canonical.children().to_vec());
                }
                _ => {
                    // c is not a variable or a constant, define a new variable for it
                    let v = self.define_with_var(c, mngr);
                    rec.push(v);
                }
            }
        }
        mngr.concat(rec)
    }

    fn define_with_var(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        let v = if let Some(v) = self.def_identities.get(node) {
            v.clone()
        } else {
            let v = mngr.temp_var(Sort::String);
            self.def_identities.insert(node.clone(), v.clone());
            v
        };
        mngr.var(v)
    }

    fn canonicalize_arithmetic_constraint(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_int() && rhs.sort().is_int());
        // Bring it into the form LHS <> c where c is a constant, <> is one of {<, <=, >, >=, =}
        // and LHS is a linear arithmetic term.

        let lhs = self.canonicalize_linear_arith_term(lhs.clone(), mngr)?;
        let rhs = self.canonicalize_linear_arith_term(rhs.clone(), mngr)?;

        let lhs = match lhs.kind() {
            NodeKind::Int(_) | NodeKind::Variable(_) | NodeKind::Length | NodeKind::Mul => {
                vec![lhs]
            }
            NodeKind::Add => lhs.children().to_vec(),
            _ => unreachable!("Expected linear arithmetic term but got '{}'", lhs),
        };
        let rhs = match rhs.kind() {
            NodeKind::Int(_) | NodeKind::Variable(_) | NodeKind::Length | NodeKind::Mul => {
                vec![rhs]
            }
            NodeKind::Add => rhs.children().to_vec(),
            _ => unreachable!("Expected linear arithmetic term but got '{}'", rhs),
        };
        let mut lhs_scalings = IndexMap::<Node, i64>::new();
        let mut const_rhs = 0;
        for l in lhs {
            match l.kind() {
                NodeKind::Int(i) => const_rhs -= *i,
                NodeKind::Variable(_) | NodeKind::Length => {
                    *lhs_scalings.entry(l).or_default() += 1;
                }
                NodeKind::Mul => {
                    debug_assert!(l.children().len() == 2);
                    let mut iter = l.children().iter();
                    let i = iter.next().unwrap();
                    let v = iter.next().unwrap();
                    match (i.kind(), v.kind()) {
                        (NodeKind::Int(i), NodeKind::Variable(_))
                        | (NodeKind::Int(i), NodeKind::Length)
                        | (NodeKind::Variable(_), NodeKind::Int(i))
                        | (NodeKind::Length, NodeKind::Int(i)) => {
                            *lhs_scalings.entry(v.clone()).or_default() += *i;
                        }
                        _ => unreachable!("Expected linear term but got '{}'", l),
                    }
                }
                _ => unreachable!("Expected linear term but got '{}'", l),
            }
        }
        for r in rhs {
            match r.kind() {
                NodeKind::Int(i) => const_rhs += *i,
                NodeKind::Variable(_) | NodeKind::Length => {
                    *lhs_scalings.entry(r).or_default() -= 1;
                }
                NodeKind::Mul => {
                    debug_assert!(r.children().len() == 2);
                    let mut iter = r.children().iter();
                    let i = iter.next().unwrap();
                    let v = iter.next().unwrap();
                    match (i.kind(), v.kind()) {
                        (NodeKind::Int(i), NodeKind::Variable(_))
                        | (NodeKind::Variable(_), NodeKind::Int(i)) => {
                            *lhs_scalings.entry(v.clone()).or_default() -= *i;
                        }
                        _ => unreachable!("Expected linear term but got '{}'", r),
                    }
                }
                _ => unreachable!("Expected linear term but got '{}'", r),
            }
        }
        let mut canonical_lhs = Vec::with_capacity(lhs_scalings.len());
        for (v, i) in lhs_scalings {
            if i == 0 {
                continue;
            }
            let scaling = mngr.int(i);
            let scaled = mngr.mul(vec![scaling, v]);
            canonical_lhs.push(scaled);
        }
        let canonical_lhs = match canonical_lhs.len() {
            0 => mngr.int(0),
            1 => canonical_lhs.pop().unwrap(),
            _ => mngr.add(canonical_lhs),
        };
        let canonical_rhs = mngr.int(const_rhs);
        match node.kind() {
            NodeKind::Eq => {
                let canonical = mngr.eq(canonical_lhs, canonical_rhs);
                if pol {
                    Ok(canonical)
                } else {
                    Ok(mngr.not(canonical))
                }
            }
            NodeKind::Lt if pol => Ok(mngr.lt(canonical_lhs, canonical_rhs)),
            NodeKind::Lt if !pol => Ok(mngr.ge(canonical_lhs, canonical_rhs)),
            NodeKind::Le if pol => Ok(mngr.le(canonical_lhs, canonical_rhs)),
            NodeKind::Le if !pol => Ok(mngr.gt(canonical_lhs, canonical_rhs)),
            NodeKind::Gt if pol => Ok(mngr.gt(canonical_lhs, canonical_rhs)),
            NodeKind::Gt if !pol => Ok(mngr.le(canonical_lhs, canonical_rhs)),
            NodeKind::Ge if pol => Ok(mngr.ge(canonical_lhs, canonical_rhs)),
            NodeKind::Ge if !pol => Ok(mngr.lt(canonical_lhs, canonical_rhs)),
            _ => unreachable!("Expected comparison but got '{}'", node),
        }
    }

    /// Takes a node representing a linear arithmetic term and brings it into canonical form.
    /// The canonical form is a sum of terms of the form `c` or `c * v` where c is a constant and v is either an integer variable or the length of a string variable.
    fn canonicalize_linear_arith_term(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(
            node.sort().is_int(),
            "Expected integer term but got '{}'",
            node
        );
        match node.kind() {
            NodeKind::Variable(v) => {
                if v.sort().is_int() {
                    Ok(node)
                } else {
                    Err(NodeError::SortMismatch(node.clone(), Sort::Int, v.sort()))
                }
            }
            NodeKind::Int(_) => Ok(node),
            NodeKind::Add => {
                let mut sums = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    let canonical = self.canonicalize_linear_arith_term(c.clone(), mngr)?;
                    if canonical.kind() == &NodeKind::Add {
                        // flatten the sum
                        sums.extend(canonical.children().to_vec());
                    } else {
                        sums.push(canonical);
                    }
                }
                Ok(mngr.add(sums))
            }
            NodeKind::Neg => {
                debug_assert!(node.children().len() == 1);
                // rewrite (- t) as (-1 * t)
                let negone = mngr.int(-1);
                let as_mult = mngr.mul(vec![negone, node.clone()]);
                self.canonicalize_linear_arith_term(as_mult, mngr)
            }
            NodeKind::Sub => {
                // rewrite (- t1 ... tn) as (+ (- t1) ... (- tn))
                let norm = node
                    .children()
                    .iter()
                    .map(|s| mngr.neg(s.clone()))
                    .collect();
                let as_addition = mngr.add(norm);
                self.canonicalize_linear_arith_term(as_addition, mngr)
            }
            NodeKind::Mul => {
                let canonicalized = node
                    .children()
                    .into_iter()
                    .map(|c| self.canonicalize_linear_arith_term(c.clone(), mngr))
                    .collect::<Result<Vec<Node>, _>>()?;
                // distribute the multiplication, abort if we have non-linear terms

                let mut left = canonicalized.first().unwrap().clone();
                for right in canonicalized.iter().skip(1) {
                    // left and right are in canonical form, i.e. linear terms.
                    // We build the cartesian product of the two terms and add them.
                    match (left.kind(), right.kind()) {
                        (NodeKind::Variable(v), NodeKind::Int(1))
                        | (NodeKind::Int(1), NodeKind::Variable(v)) => {
                            mngr.var(v.clone());
                        }
                        (NodeKind::Int(_), NodeKind::Variable(_))
                        | (NodeKind::Int(_), NodeKind::Length) => {
                            left = mngr.mul(vec![left, right.clone()]);
                        }
                        (NodeKind::Variable(_), NodeKind::Int(_))
                        | (NodeKind::Length, NodeKind::Int(_)) => {
                            left = mngr.mul(vec![right.clone(), left]);
                        }
                        (NodeKind::Int(l), NodeKind::Int(r)) => {
                            left = mngr.int(l * r);
                        }
                        (NodeKind::Variable(_), NodeKind::Variable(_)) => {
                            return Err(NodeError::NonLinearArithmetic(node))
                        }
                        (NodeKind::Int(_), NodeKind::Add) => {
                            // scale all terms in the sum
                            let mut scaled = Vec::with_capacity(right.children().len());
                            for c in right.children() {
                                let scaled_c = mngr.mul(vec![left.clone(), c.clone()]);
                                let canon = self.canonicalize_linear_arith_term(scaled_c, mngr)?;
                                scaled.push(canon);
                            }
                        }
                        (NodeKind::Add, NodeKind::Int(_)) => {
                            // scale all terms in the sum
                            let mut scaled = Vec::with_capacity(left.children().len());
                            for c in right.children() {
                                let scaled_c = mngr.mul(vec![right.clone(), c.clone()]);
                                let canon = self.canonicalize_linear_arith_term(scaled_c, mngr)?;
                                scaled.push(canon);
                            }
                        }
                        _ => {
                            return Err(NodeError::NotWellFormed(node));
                        }
                    }
                }
                debug_assert!(
                    matches!(left.kind(), &NodeKind::Variable(_))
                        || matches!(left.kind(), &NodeKind::Length)
                        || matches!(left.kind(), &NodeKind::Mul)
                        || matches!(left.kind(), &NodeKind::Int(_))
                        || matches!(left.kind(), &NodeKind::Add),
                    "Expected linear term but got '{}'",
                    left
                );
                Ok(left)
            }
            NodeKind::Length => self.canonicalize_string_length(node, mngr),
            _ => Err(NodeError::NotWellFormed(node)),
        }
    }

    /// Canonicalizes a node of the form (length t), where t is a string term.
    /// If t is of the form (concat r1 ... rm), the result is a new node (+ (length r1) ... (length rm))
    /// If t is a variable, the result is the same node.
    /// If t is a constant, the result is a new node with the constant length.
    fn canonicalize_string_length(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.sort().is_int());
        debug_assert!(node.kind() == &NodeKind::Length);
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();
        match child.kind() {
            NodeKind::String(s) => {
                let len = s.chars().count();
                assert!(len < i64::MAX as usize, "String '{}' too long", s);
                Ok(mngr.int(len as i64))
            }
            NodeKind::Variable(v) => {
                if v.sort().is_string() {
                    Ok(node)
                } else {
                    Err(NodeError::SortMismatch(
                        node.clone(),
                        Sort::String,
                        v.sort(),
                    ))
                }
            }
            NodeKind::Concat => {
                let mut sums = Vec::with_capacity(child.children().len());
                let canonical = self.canonicalize_concat(child.clone(), mngr);
                for c in canonical.children() {
                    let len = mngr.str_len(c.clone());
                    let canonical_len = self.canonicalize_string_length(len, mngr)?;
                    sums.push(canonical_len);
                }
                Ok(mngr.add(sums))
            }
            _ => Err(NodeError::NotWellFormed(node)),
        }
    }
}

#[derive(Debug, Clone)]
pub enum CanonicalAtom {
    WordEquation(WordEquation),
    InRe(RegularConstraint),
    FactorConstraint(FactorConstraint),
    Linear(LinearConstraint),
}
impl Display for CanonicalAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CanonicalAtom::WordEquation(we) => write!(f, "{}", we),
            CanonicalAtom::InRe(re) => write!(f, "{}", re),
            CanonicalAtom::FactorConstraint(fc) => write!(f, "{}", fc),
            CanonicalAtom::Linear(lc) => write!(f, "{}", lc),
        }
    }
}

#[derive(Debug, Clone)]
pub enum CanonicalLit {
    Positive(CanonicalAtom),
    Negative(CanonicalAtom),
}

impl Display for CanonicalLit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CanonicalLit::Positive(atom) => write!(f, "{}", atom),
            CanonicalLit::Negative(atom) => write!(f, "!({})", atom),
        }
    }
}

#[derive(Default)]
pub(super) struct CanonicalMapper {
    node2ir: IndexMap<Node, CanonicalAtom>,
    patterns: IndexMap<Node, Pattern>,
}

impl CanonicalMapper {
    pub fn lit2ir(&mut self, lit: &Node) -> Option<CanonicalLit> {
        let converted = if lit.is_atomic() {
            CanonicalLit::Positive(self.atom2ir(lit)?)
        } else {
            debug_assert!(*lit.kind() == NodeKind::Not);
            debug_assert!(lit.children().len() == 1);
            CanonicalLit::Negative(self.atom2ir(&lit[0])?)
        };
        Some(converted)
    }

    pub fn atom2ir(&mut self, atom: &Node) -> Option<CanonicalAtom> {
        let converted = match atom.kind() {
            NodeKind::Eq => {
                debug_assert!(atom.children().len() == 2);
                let l = &atom[0];
                let r = &atom[1];
                debug_assert!(l.sort() == r.sort());
                if l.sort().is_string() {
                    self.convert_word_equation(l, r)
                } else if l.sort().is_int() {
                    self.convert_linear_constraint(atom)
                } else {
                    unreachable!()
                }
            }
            NodeKind::Ge | NodeKind::Gt | NodeKind::Le | NodeKind::Lt => {
                self.convert_linear_constraint(atom)
            }
            NodeKind::InRe => {
                debug_assert!(atom.children().len() == 2);
                let l = &atom[0];
                let r = &atom[1];
                self.convert_in_re(l, r)
            }
            _ => return None,
        };
        self.node2ir.insert(atom.clone(), converted.clone());
        Some(converted)
    }

    fn convert_word_equation(&mut self, lhs: &Node, rhs: &Node) -> CanonicalAtom {
        let lhs = self.convert_pattern(lhs);
        let rhs = self.convert_pattern(rhs);
        CanonicalAtom::WordEquation(WordEquation::new(lhs, rhs))
    }

    fn convert_pattern(&mut self, node: &Node) -> Pattern {
        if let Some(p) = self.patterns.get(node) {
            return p.clone();
        }
        let mut result = Pattern::empty();
        let mut iter = SymbolIterator::new(node);
        while let Some(s) = iter.next() {
            match s {
                crate::node::utils::Symbol::Const(c) => result.push_char(c),
                crate::node::utils::Symbol::Variable(rc) => result.push_var(rc.clone()),
            };
        }

        self.patterns.insert(node.clone(), result.clone());
        result
    }

    fn convert_in_re(&self, lhs: &Node, rhs: &Node) -> CanonicalAtom {
        let var = lhs.as_variable().expect("Not in canonical form");
        if let NodeKind::Regex(re) = rhs.kind() {
            CanonicalAtom::InRe(RegularConstraint::new(var.clone(), re.clone()))
        } else {
            unreachable!("Not in canonical form")
        }
    }

    fn convert_linear_constraint(&self, node: &Node) -> CanonicalAtom {
        assert!(node.children().len() == 2);
        let lhs = self.convert_linarith_lerm(&node[0]);
        let rhs = node[1].as_int_const().expect("Not in canonical form");
        let op = match node.kind() {
            NodeKind::Eq => LinearOperator::Eq,
            NodeKind::Lt => LinearOperator::Less,
            NodeKind::Le => LinearOperator::Leq,
            NodeKind::Gt => LinearOperator::Greater,
            NodeKind::Ge => LinearOperator::Geq,
            _ => unreachable!("Not a linear constraint"),
        };
        let lc = LinearConstraint::new(lhs, op, rhs as isize);
        CanonicalAtom::Linear(lc)
    }

    fn convert_linarith_lerm(&self, node: &Node) -> LinearArithTerm {
        match node.kind() {
            NodeKind::Int(i) => LinearArithTerm::from_const(*i as isize),
            NodeKind::Variable(var) => LinearArithTerm::from_var(var.clone()),
            NodeKind::Length => {
                assert!(node.children().len() == 1);
                if let Some(v) = node[0].as_variable() {
                    LinearArithTerm::from_var(v.clone())
                } else {
                    unreachable!("Not in canonical form")
                }
            }
            NodeKind::Add => {
                let mut result = LinearArithTerm::new();
                for c in node.children() {
                    let term = self.convert_linarith_lerm(c);
                    result.add(term);
                }
                result
            }
            NodeKind::Neg => {
                assert!(node.children().len() == 1);
                let mut res = self.convert_linarith_lerm(&node[0]);
                res.multiply_constant(-1);
                res
            }
            NodeKind::Sub => {
                let mut result = LinearArithTerm::new();
                for c in node.children() {
                    let mut term = self.convert_linarith_lerm(c);
                    term.multiply_constant(-1);
                    result.add(term);
                }
                result
            }
            NodeKind::Mul => {
                assert!(node.children().len() == 2);
                let s = node[0].as_int_const();
                match node[1].kind() {
                    NodeKind::Variable(v) => LinearArithTerm::from_var(v.clone()),
                    NodeKind::Length => {
                        assert!(node[1].children().len() == 1);
                        let v = node[1][0].as_variable().expect("Not in canonical form");
                        LinearArithTerm::from_var_len(v.clone())
                    }
                    _ => unreachable!("Not in canonical form"),
                }
            }
            _ => unreachable!("Not in canonical form"),
        }
    }
}
