//! Conversion of nodes into canonical form.

use std::{collections::HashMap, f32::consts::E, ops::Deref};

use error::NodeError;

use crate::ir::Pattern;

use super::*;

#[derive(Default)]
struct Canonicalizer {
    /// Definitions of patterns as variables.
    /// Each key is a node representing a pattern, and the value is the variable that represents it.
    pattern_defs: HashMap<Node, Node>,
}

impl Canonicalizer {
    pub fn canonical(&mut self, node: Node, mngr: &mut NodeManager) -> Result<Node, NodeError> {
        match node.kind() {
            NodeKind::Or => {
                let rec = node
                    .children()
                    .into_iter()
                    .map(|c| self.canonical(c.clone(), mngr))
                    .collect::<Result<Vec<Node>, _>>();

                Ok(mngr.or(rec?))
            }
            NodeKind::And => {
                let rec = node
                    .children()
                    .into_iter()
                    .map(|c| self.canonical(c.clone(), mngr))
                    .collect::<Result<Vec<Node>, _>>();
                Ok(mngr.and(rec?))
            }
            NodeKind::Imp | NodeKind::Equiv => {
                return Err(NodeError::NotInNegationNormalForm(node))
            }
            NodeKind::Not => {
                debug_assert!(node.children().len() == 1);
                let child = node.children().first().unwrap();
                match child.kind() {
                    NodeKind::Or
                    | NodeKind::And
                    | NodeKind::Imp
                    | NodeKind::Equiv
                    | NodeKind::Not => return Err(NodeError::NotInNegationNormalForm(node)),

                    NodeKind::Variable(_)
                    | NodeKind::Eq
                    | NodeKind::InRe
                    | NodeKind::PrefixOf
                    | NodeKind::SuffixOf
                    | NodeKind::Contains
                    | NodeKind::Lt
                    | NodeKind::Le
                    | NodeKind::Gt
                    | NodeKind::Ge => self.canonicalize_lit(child.clone(), false, mngr),
                    /* these are terms and cannot occur above atomic propositions */
                    NodeKind::Bool(_)
                    | NodeKind::String(_)
                    | NodeKind::Int(_)
                    | NodeKind::Regex(_)
                    | NodeKind::Add
                    | NodeKind::Sub
                    | NodeKind::Mul
                    | NodeKind::Concat
                    | NodeKind::Length => Err(NodeError::NotWellFormed(node)),
                }
            }

            /* Atomic formulas */
            NodeKind::Variable(_)
            | NodeKind::Eq
            | NodeKind::InRe
            | NodeKind::PrefixOf
            | NodeKind::SuffixOf
            | NodeKind::Contains
            | NodeKind::Lt
            | NodeKind::Le
            | NodeKind::Gt
            | NodeKind::Ge => self.canonicalize_lit(node, true, mngr),
            /* these are terms and cannot occur above atomic propositions */
            NodeKind::Bool(_)
            | NodeKind::String(_)
            | NodeKind::Int(_)
            | NodeKind::Regex(_)
            | NodeKind::Add
            | NodeKind::Sub
            | NodeKind::Mul
            | NodeKind::Concat
            | NodeKind::Length => Err(NodeError::NotWellFormed(node)),
        }
    }

    fn canonicalize_lit(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.is_atomic());

        match node.kind() {
            NodeKind::Variable(v) => {
                debug_assert!(v.sort().is_bool());
                Ok(node)
            }
            NodeKind::InRe => self.canonicalize_in_re(node, pol, mngr),
            NodeKind::Contains => todo!(),
            NodeKind::PrefixOf => todo!(),
            NodeKind::SuffixOf => todo!(),
            NodeKind::Eq => todo!(),
            NodeKind::Gt | NodeKind::Ge | NodeKind::Lt | NodeKind::Le => todo!(),
            _ => unreachable!("Expected atomic formula"),
        }
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
        if let Some(v) = self.replace_pattern(pat.clone(), mngr) {
            let inre = mngr.in_re(v, node.children().last().unwrap().clone());
            if pol {
                return Ok(inre);
            } else {
                return Ok(mngr.not(inre));
            }
        } else {
            Ok(node)
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

    fn replace_pattern(&mut self, p: Node, mngr: &mut NodeManager) -> Option<Node> {
        let aspattern = mngr.patternize(&p)?;
        if aspattern.is_variable() || aspattern.is_constant() {
            return Some(p);
        } else {
            match self.pattern_defs.get(&p) {
                Some(v) => Some(v.clone()),
                None => {
                    let v = mngr.temp_var(Sort::String);
                    let vv = mngr.var(v);
                    self.pattern_defs.insert(p.clone(), vv.clone());
                    Some(vv)
                }
            }
        }
    }

    fn canonicalize_linear(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.children().len() == 2);
        todo!()
    }

    fn canonical_arith(&mut self, node: Node, mngr: &mut NodeManager) -> Result<Node, NodeError> {
        match node.kind() {
            NodeKind::Add => {
                let mut rec: Vec<Node> = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    rec.push(self.canonical_arith(c.clone(), mngr)?);
                }
                Ok(mngr.add(rec))
            }
            NodeKind::Sub => {
                let mut rec: Vec<Node> = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    rec.push(self.canonical_arith(c.clone(), mngr)?);
                }
                Ok(mngr.sub(rec))
            }
            _ => unreachable!("Expected arithmetic expression"),
        }
    }
}
