//! Conversion of nodes into canonical form.

pub use int::*;

pub use string::*;

use crate::{
    context::{Sort, Sorted},
    node::{self, NodeManager},
};

use super::*;
use indexmap::IndexMap;
use node::{error::NodeError, utils::SymbolIterator, Node, NodeKind};

use std::{collections::HashMap, rc::Rc};

pub fn canonicalize(node: &Node, mngr: &mut NodeManager) -> Result<Formula, NodeError> {
    let mut canonicalizer = Canonicalizer::default();
    canonicalizer.canonicalize(node, mngr)
}

#[derive(Default)]
struct Canonicalizer {
    /// Identities of the form t = v, where t is a term and v is a variable.
    /// Theses dentities are introduced during the canonicalization process if a term is not in canonical form.
    def_identities: HashMap<Node, Rc<Variable>>,
    patterns: IndexMap<Node, Pattern>,
    cache: IndexMap<Node, Formula>,
}

impl Canonicalizer {
    /// Brings all literals into canonical form.
    fn canonicalize(&mut self, node: &Node, mngr: &mut NodeManager) -> Result<Formula, NodeError> {
        if let Some(f) = self.cache.get(node) {
            return Ok(f.clone());
        }
        let canon = if node.is_literal() {
            match self.canonicalize_lit(node, mngr)? {
                Some(lit) => Ok(Formula::new(FormulaKind::Literal(lit), node.clone())),
                None => Ok(Formula::unsupported(node.clone())),
            }
        } else if node.is_bool_fun() {
            match node.kind() {
                NodeKind::And | NodeKind::Or => {
                    let rec = node
                        .children()
                        .into_iter()
                        .map(|c| self.canonicalize(c, mngr))
                        .collect::<Result<Vec<Formula>, _>>();
                    let kind = match node.kind() {
                        NodeKind::And => FormulaKind::And(rec?),
                        NodeKind::Or => FormulaKind::Or(rec?),
                        _ => unreachable!(),
                    };
                    Ok(Formula::new(kind, node.clone()))
                }
                NodeKind::Not | NodeKind::Imp | NodeKind::Equiv => {
                    return Err(NodeError::NotInNegationNormalForm(node.clone()))
                }
                _ => unreachable!("Expected boolean function"),
            }
        } else {
            // The node is a term, this should not happen in a well-formed formula.
            return Err(NodeError::NotWellFormed(node.clone()));
        }?;
        self.cache.insert(node.clone(), canon.clone());
        Ok(canon)
    }

    fn canonicalize_atom(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Option<Atom>, NodeError> {
        debug_assert!(node.is_literal());
        debug_assert!(node.is_atomic());
        let atom = match node.kind() {
            NodeKind::Variable(v) => {
                debug_assert!(v.sort().is_bool());
                Some(Atom::new(AtomKind::Boolvar(v.clone()), node.clone()))
            }
            NodeKind::Bool(_) => None,
            NodeKind::InRe => Some(self.canonicalize_in_re(node, mngr)?),
            NodeKind::Contains => Some(self.canonicalize_contains(node, mngr)?),
            NodeKind::PrefixOf => Some(self.canonicalize_prefixof(node, mngr)?),
            NodeKind::SuffixOf => Some(self.canonicalize_suffixof(node, mngr)?),
            NodeKind::Eq => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap().sort();
                let rhs = node.children().last().unwrap().sort();
                if lhs == rhs {
                    if lhs.is_string() {
                        Some(self.canonicalize_weq(node, mngr)?)
                    } else if lhs.is_int() {
                        Some(self.canonicalize_arithmetic_constraint(node, mngr)?)
                    } else {
                        return Err(NodeError::NotWellFormed(node.clone()));
                    }
                } else {
                    return Err(NodeError::SortMismatch(node.clone(), lhs, rhs));
                }
            }
            NodeKind::Gt | NodeKind::Ge | NodeKind::Lt | NodeKind::Le => {
                Some(self.canonicalize_arithmetic_constraint(node, mngr)?)
            }
            _ if node.is_bool_fun() => unreachable!("Expected atomic formula but got '{}'", node),
            _ => None,
        };
        Ok(atom)
    }

    fn canonicalize_lit(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Option<Literal>, NodeError> {
        debug_assert!(node.is_literal());
        if *node.kind() == NodeKind::Not {
            let atom = node.children().first().unwrap();
            let catom = self.canonicalize_atom(atom, mngr)?;
            match catom {
                Some(catom) => match atom.kind() {
                    NodeKind::Contains | NodeKind::PrefixOf | NodeKind::SuffixOf
                        if !matches!(catom.kind(), AtomKind::FactorConstraint(_)) =>
                    {
                        // Unsupported: These introduce universal quantifiers when negated
                        Ok(None)
                    }
                    _ => Ok(Some(Literal::new(false, catom))),
                },
                None => Ok(None),
            }
        } else {
            let catom = self.canonicalize_atom(node, mngr)?;
            match catom {
                Some(catom) => Ok(Some(Literal::new(true, catom))),
                None => Ok(None),
            }
        }
    }

    fn canonicalize_in_re(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Atom, NodeError> {
        debug_assert!(*node.kind() == NodeKind::InRe);
        debug_assert!(node.children().len() == 2);

        let pat = node.children().first().unwrap();
        let v = if let Some(v) = pat.as_variable() {
            debug_assert!(v.sort().is_string());
            v.clone()
        } else {
            self.define_with_var(pat, mngr)
        };
        if let NodeKind::Regex(re) = node[1].kind() {
            let atom = AtomKind::InRe(RegularConstraint::new(v, re.clone()));
            Ok(Atom::new(atom, node.clone()))
        } else {
            return Err(NodeError::NotWellFormed(node.clone()));
        }
    }

    fn canonicalize_prefixof(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Atom, NodeError> {
        debug_assert!(*node.kind() == NodeKind::PrefixOf);
        // PrefixOf(r, s) <--> EX t. r = s ++ t
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let r = node.children().first().unwrap();
        let s = node.children().last().unwrap();
        // If `s`  is constant, then this is a regular expression constraint r \in .*s.*
        if let Some(s) = node[1].as_str_const() {
            let v = if let Some(v) = r.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(r, mngr)
            };
            Ok(Atom::new(
                AtomKind::FactorConstraint(RegularFactorConstraint::prefixof(v, s.to_string())),
                node.clone(),
            ))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![s.clone(), t.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_suffixof(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Atom, NodeError> {
        debug_assert!(*node.kind() == NodeKind::SuffixOf);
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let r = node.children().first().unwrap();
        let s = node.children().last().unwrap();
        // If `s`  is constant, then this is a regular expression constraint r \in .*s.*
        if let Some(s) = node[1].as_str_const() {
            let v = if let Some(v) = r.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(r, mngr)
            };
            Ok(Atom::new(
                AtomKind::FactorConstraint(RegularFactorConstraint::suffixof(v, s.to_string())),
                node.clone(),
            ))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![t.clone(), s.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_contains(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Atom, NodeError> {
        debug_assert!(*node.kind() == NodeKind::Contains);
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let r = node.children().first().unwrap();
        let s = node.children().last().unwrap();
        // If `s`  is constant, then this is a regular expression constraint r \in .*s.*
        if let Some(s) = node[1].as_str_const() {
            let v = if let Some(v) = r.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(r, mngr)
            };
            Ok(Atom::new(
                AtomKind::FactorConstraint(RegularFactorConstraint::contains(v, s.to_string())),
                node.clone(),
            ))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let u = mngr.temp_var(Sort::String);
            let u = mngr.var(u);
            let rhs = mngr.concat(vec![t.clone(), s.clone(), u.clone()]);
            let eq = mngr.eq(r.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_pattern(&mut self, node: &Node) -> Pattern {
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

    fn canonicalize_weq(&mut self, node: &Node, mngr: &mut NodeManager) -> Result<Atom, NodeError> {
        debug_assert!(*node.kind() == NodeKind::Eq);
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_string());
        debug_assert!(rhs.sort().is_string());
        let lhs = self.canonicalize_concat(lhs.clone(), mngr);
        let rhs = self.canonicalize_concat(rhs.clone(), mngr);
        let weq = WordEquation::new(lhs, rhs);
        Ok(Atom::new(AtomKind::WordEquation(weq), node.clone()))
    }

    /// Canocalizes nodes of the form (concat t1 ... tn). The result is a new node (concat r1 ... rm)
    /// where each ri is a einther a (string) variable or a constant. Does the following:
    /// - If any of node ti is not a variable or a constant, ti is replaced by a new variable ri and the identity ti = ri is stored.
    /// - If ti is a concatenation, it is recursively canonicalized and flattened.
    /// Returns a Pattern representing the canonical form of the concatenation.
    fn canonicalize_concat(&mut self, node: Node, mngr: &mut NodeManager) -> Pattern {
        if let Some(p) = self.patterns.get(&node) {
            return p.clone();
        }
        debug_assert!(
            *node.kind() == NodeKind::Concat || node.is_var() || node.is_const(),
            "Expected concatenation, variable, or constant but got '{}'",
            node
        );
        if let Some(v) = node.as_variable() {
            Pattern::variable(v.clone())
        } else if let Some(s) = node.as_str_const() {
            Pattern::constant(s)
        } else if *node.kind() == NodeKind::Concat {
            let mut rec = Pattern::empty();
            for c in node.children() {
                let canon = self.canonicalize_concat(c.clone(), mngr);
                rec.extend(canon);
            }
            self.patterns.insert(node.clone(), rec.clone());
            rec
        } else {
            // define a new variable for the node
            debug_assert!(node.sort().is_string());
            let v = self.define_with_var(&node, mngr);
            Pattern::variable(v)
        }
    }

    fn define_with_var(&mut self, node: &Node, mngr: &mut NodeManager) -> Rc<Variable> {
        let v = if let Some(v) = self.def_identities.get(node) {
            v.clone()
        } else {
            let v = mngr.temp_var(Sort::String);
            self.def_identities.insert(node.clone(), v.clone());
            v
        };
        v
    }

    fn canonicalize_arithmetic_constraint(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Result<Atom, NodeError> {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_int() && rhs.sort().is_int());
        // Bring it into the form LHS <> c where c is a constant, <> is one of {<, <=, >, >=, =}
        // and LHS is a linear arithmetic term.

        let lhs = self.canonicalize_linear_arith_term(lhs.clone(), mngr)?;
        let rhs = self.canonicalize_linear_arith_term(rhs.clone(), mngr)?;
        let (clhs, crhs) = self.normalize_linear(lhs, rhs);

        let op = match node.kind() {
            NodeKind::Eq => ArithOperator::Eq,
            NodeKind::Lt => ArithOperator::Less,
            NodeKind::Le => ArithOperator::Leq,
            NodeKind::Gt => ArithOperator::Greater,
            NodeKind::Ge => ArithOperator::Geq,
            _ => unreachable!("Not a linear constraint"),
        };
        let lc = LinearConstraint::new(clhs, op, crhs);
        Ok(Atom::new(AtomKind::Linear(lc), node.clone()))
    }

    /// Takes a node representing a linear arithmetic term and brings it into canonical form.
    /// The canonical form is a sum of terms of the form `c` or `c * v` where c is a constant and v is either an integer variable or the length of a string variable.
    fn canonicalize_linear_arith_term(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Result<LinearArithTerm, NodeError> {
        debug_assert!(
            node.sort().is_int(),
            "Expected integer term but got '{}'",
            node
        );
        match node.kind() {
            NodeKind::Variable(v) => {
                if v.sort().is_int() {
                    Ok(LinearArithTerm::from_var(v.clone()))
                } else {
                    Err(NodeError::SortMismatch(node.clone(), Sort::Int, v.sort()))
                }
            }
            NodeKind::Int(i) => Ok(LinearArithTerm::from_const(*i as isize)),
            NodeKind::Add => {
                let mut sum = LinearArithTerm::new();
                for c in node.children() {
                    let canonical = self.canonicalize_linear_arith_term(c.clone(), mngr)?;
                    sum.add(canonical);
                }
                Ok(sum)
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
                // distribute the multiplication, abort if we have non-linear terms

                let mut res = LinearArithTerm::from_const(1);
                for e in node.children() {
                    let next = self.canonicalize_linear_arith_term(e.clone(), mngr)?;
                    res = match LinearArithTerm::multiply(res, next) {
                        Some(r) => r,
                        None => {
                            return Err(NodeError::NonLinearArithmetic(node.clone()));
                        }
                    }
                }
                Ok(res)
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
    ) -> Result<LinearArithTerm, NodeError> {
        debug_assert!(node.sort().is_int());
        debug_assert!(node.kind() == &NodeKind::Length);
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();
        match child.kind() {
            NodeKind::String(s) => {
                let len = s.chars().count();
                assert!(len < i64::MAX as usize, "String '{}' too long", s);
                Ok(LinearArithTerm::from_const(len as isize))
            }
            NodeKind::Variable(v) => {
                if v.sort().is_string() {
                    Ok(LinearArithTerm::from_var_len(v.clone()))
                } else {
                    Err(NodeError::SortMismatch(
                        node.clone(),
                        Sort::String,
                        v.sort(),
                    ))
                }
            }
            NodeKind::Concat => {
                let canonical = self.canonicalize_concat(child.clone(), mngr);
                let mut res = LinearArithTerm::from_const(0);
                for c in canonical.symbols() {
                    let add = match c {
                        Symbol::Constant(_) => LinearArithTerm::from_const(1),
                        Symbol::Variable(rc) => LinearArithTerm::from_var_len(rc.clone()),
                    };
                    res.add(add);
                }
                Ok(res)
            }
            _ => Err(NodeError::NotWellFormed(node)),
        }
    }

    fn normalize_linear(
        &self,
        lhs: LinearArithTerm,
        rhs: LinearArithTerm,
    ) -> (LinearArithTerm, isize) {
        let mut new_lhs = LinearArithTerm::new();
        let mut rhs_const = 0;
        for term in lhs.into_iter() {
            match &term {
                LinearSummand::Const(c) => rhs_const -= c,
                LinearSummand::Mult(_, _) => new_lhs.add_summand(term),
            }
        }
        for term in rhs.into_iter() {
            match &term {
                LinearSummand::Const(c) => rhs_const += c,
                LinearSummand::Mult(_, _) => new_lhs.add_summand(term.flip_sign()),
            }
        }
        (new_lhs, rhs_const)
    }
}
