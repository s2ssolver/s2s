//! Simplification for variables the occur only once in the formula.

use std::{collections::HashMap, rc::Rc};

use regulaer::re::Regex;

use crate::{context::Variable, node::NodeKind};

use super::*;

/// Finds variables that occur only once in the formula and replaces them with a constant, based on the literal they occur in.
#[derive(Clone, Default)]
pub struct IndependentVariableAssignment {
    vcount: HashMap<Rc<Variable>, usize>,
}

impl IndependentVariableAssignment {
    fn count_variables(node: &Node, counter: &mut HashMap<Rc<Variable>, usize>) {
        match node.kind() {
            NodeKind::Variable(v) => {
                *counter.entry(v.clone()).or_default() += 1;
            }
            _ => {
                for child in node.children() {
                    Self::count_variables(child, counter);
                }
            }
        }
    }

    fn independent(&self, v: &Rc<Variable>) -> bool {
        self.vcount.get(v).map_or(false, |&c| c == 1)
    }

    fn try_reduce_eq(
        &self,
        lhs: &Node,
        rhs: &Node,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<NodeSubstitution> {
        match (lhs.kind(), rhs.kind()) {
            (NodeKind::Variable(v), rhs_v) | (rhs_v, NodeKind::Variable(v))
                if self.independent(v) =>
            {
                match rhs_v {
                    NodeKind::String(s) => {
                        let mut subs = NodeSubstitution::default();
                        let rhs = if pol {
                            rhs.clone()
                        } else {
                            if s == "" {
                                mngr.const_str("a")
                            } else {
                                mngr.const_str("")
                            }
                        };
                        subs.add(lhs.clone(), rhs, mngr);
                        Some(subs)
                    }
                    NodeKind::Int(_) => todo!(),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn try_reduce_reg_membership(
        &self,
        lhs: &Node,
        regex: &Regex,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<NodeSubstitution> {
        match lhs.kind() {
            NodeKind::Variable(v) if self.independent(v) => {
                let mut subs = NodeSubstitution::default();
                // TODO: CHECK IF a empty in lang and return accordingly

                let regex = if pol {
                    regex.clone()
                } else {
                    mngr.re_builder().comp(regex.clone())
                };
                let nfa = mngr.get_nfa(&regex);

                let rhs = nfa.sample()?;

                if pol {
                    debug_assert!(regex.accepts(&rhs));
                } else {
                    debug_assert!(!regex.accepts(&rhs));
                }
                let rhs_str = rhs.iter().collect::<String>();
                debug_assert!(rhs_str.len() == rhs.len());
                let rhs = mngr.const_string(rhs_str);
                subs.add(lhs.clone(), rhs, mngr);
                return Some(subs);
            }
            _ => (),
        }

        None
    }

    fn apply(&self, atom: &Node, polarity: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        debug_assert!(atom.is_atomic(), "{} is not an atomic formula", atom);
        match atom.kind() {
            NodeKind::Variable(rc) => {
                let mut subs = NodeSubstitution::default();
                if self.independent(rc) {
                    subs.add(atom.clone(), mngr.ttrue(), mngr);
                    return Some(Simplification::new(subs, None));
                }
            }
            NodeKind::Eq => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();
                if let Some(subs) = self.try_reduce_eq(lhs, rhs, polarity, mngr) {
                    return Some(Simplification::new(subs, None));
                }
            }
            NodeKind::InRe => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();
                if let NodeKind::Regex(re) = rhs.kind() {
                    if let Some(subs) = self.try_reduce_reg_membership(lhs, re, polarity, mngr) {
                        return Some(Simplification::new(subs, None));
                    }
                } else {
                    unreachable!("Membership atom with non-regex rhs");
                }
            }
            NodeKind::PrefixOf | NodeKind::SuffixOf | NodeKind::Contains => {
                log::warn!("TODO: Implement independent variable reductions for PrefixOf, SuffixOf, Contains")
            }
            _ => (),
        }
        None
    }
}

impl SimpRule for IndependentVariableAssignment {
    fn apply(&self, node: &Node, _: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if node.is_literal() {
            match node.kind() {
                NodeKind::Not => {
                    let child = node.children().first().unwrap();
                    self.apply(child, false, mngr)
                }
                _ => self.apply(node, true, mngr),
            }
        } else {
            None
        }
    }

    fn init(&mut self, root: &Node) {
        Self::count_variables(root, &mut self.vcount);
    }

    fn name(&self) -> &str {
        "IndependentVariableAssignment"
    }
}
