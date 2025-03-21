//! Simplification for variables the occur only once in the formula.

use std::{collections::HashMap, rc::Rc};

use smtlib_str::{re::Regex, sampling::sample_nfa};

use crate::node::{NodeKind, Variable};

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
    ) -> Option<VarSubstitution> {
        match (lhs.kind(), rhs.kind()) {
            (NodeKind::Variable(v), rhs_v) | (rhs_v, NodeKind::Variable(v))
                if self.independent(v) =>
            {
                match rhs_v {
                    NodeKind::String(s) => {
                        let mut subs = VarSubstitution::default();
                        let rhs = if pol {
                            rhs.clone()
                        } else if s.is_empty() {
                            mngr.const_str("a")
                        } else {
                            mngr.empty_string()
                        };
                        subs.add(v.clone(), rhs);
                        Some(subs)
                    }
                    NodeKind::Int(i) => {
                        let mut subs = VarSubstitution::default();
                        let rhs = if pol {
                            rhs.clone()
                        } else if *i != 0 {
                            mngr.const_int(0)
                        } else {
                            mngr.const_int(1)
                        };
                        subs.add(v.clone(), rhs);
                        Some(subs)
                    }
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
    ) -> Option<VarSubstitution> {
        match lhs.kind() {
            NodeKind::Variable(v) if self.independent(v) => {
                let mut subs = VarSubstitution::default();
                // TODO: CHECK IF a empty in lang and return accordingly
                let regex = if pol {
                    regex.clone()
                } else {
                    mngr.re_builder().comp(regex.clone())
                };
                let nfa = mngr.get_nfa(&regex);

                let rhs = match sample_nfa(&nfa, 1000) {
                    Some(w) => w,
                    None => {
                        log::warn!("Could not sample from\n{}", nfa.dot());
                        return Some(subs); // short circuit here
                    }
                };

                debug_assert!(
                    regex.accepts(&rhs),
                    "Regex: {} does not accept '{}'",
                    regex,
                    rhs
                );

                let rhs = mngr.const_string(rhs);
                subs.add(v.clone(), rhs);
                return Some(subs);
            }
            _ => (),
        }

        None
    }

    fn apply(&self, atom: &Node, polarity: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        debug_assert!(atom.is_atomic(), "{} is not an atomic formula", atom);
        match atom.kind() {
            NodeKind::Variable(v) => {
                let mut subs = VarSubstitution::default();
                if self.independent(v) {
                    if polarity {
                        subs.add(v.clone(), mngr.ttrue());
                    } else {
                        subs.add(v.clone(), mngr.ffalse());
                    }
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
                // Cano only reduce the atom if the contained string is a constant and the container is a variable
                let contained = if NodeKind::Contains == *atom.kind() {
                    atom.children().last().unwrap()
                } else {
                    atom.children().first().unwrap()
                };
                let container = if NodeKind::Contains == *atom.kind() {
                    atom.children().first().unwrap()
                } else {
                    atom.children().last().unwrap()
                };
                if let Some(asstr) = contained.as_str_const() {
                    if let Some(v) = container.as_variable() {
                        if self.independent(v) {
                            if polarity {
                                let mut subs = VarSubstitution::default();
                                let rhs = mngr.const_string(asstr.clone());
                                subs.add(v.clone(), rhs);
                                return Some(Simplification::new(subs, None));
                            } else {
                                // abort here to not decent into the children
                                return Some(Simplification::new(VarSubstitution::default(), None));
                            }
                        }
                    }
                }
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
        self.vcount.clear();
        Self::count_variables(root, &mut self.vcount);
    }

    fn name(&self) -> &str {
        "IndependentVariableAssignment"
    }
}
