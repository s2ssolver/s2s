//! Conversion of nodes into canonical form.

use super::*;
use error::NodeError;

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

        match node.kind() {
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
                        self.canonical_arith(node, pol, mngr)
                    } else {
                        Err(NodeError::NotWellFormed(node))
                    }
                } else {
                    Err(NodeError::SortMismatch(node, lhs, rhs))
                }
            }
            NodeKind::Gt | NodeKind::Ge | NodeKind::Lt | NodeKind::Le => todo!(),
            _ => unreachable!("Expected atomic formula but got '{}'", node),
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

    fn canonicalize_linear(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        debug_assert!(node.children().len() == 2);
        todo!()
    }

    fn canonical_arith(
        &mut self,
        node: Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Result<Node, NodeError> {
        match node.kind() {
            NodeKind::Add => {
                let mut rec: Vec<Node> = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    rec.push(self.canonical_arith(c.clone(), pol, mngr)?);
                }
                Ok(mngr.add(rec))
            }
            NodeKind::Sub => {
                let mut rec: Vec<Node> = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    rec.push(self.canonical_arith(c.clone(), pol, mngr)?);
                }
                Ok(mngr.sub(rec))
            }
            _ => unreachable!("Expected arithmetic expression"),
        }
    }
}
