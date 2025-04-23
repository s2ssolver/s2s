//! Simplification for variables the occur only once in the formula.

use std::rc::Rc;

use smt_str::{re::Regex, sampling::sample_regex};

use crate::ast::NodeKind;
use crate::context::Variable;

use super::*;

/// Finds variables that occur only once in the formula and replaces them with a constant, based on the literal they occur in.
#[derive(Clone, Default, Debug)]
pub(super) struct IndependentVariableAssignment {
    vcount: IndexMap<Rc<Variable>, usize>,
}

impl IndependentVariableAssignment {
    fn count_variables(node: &Node, counter: &mut IndexMap<Rc<Variable>, usize>) {
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
        self.vcount.get(v).is_some_and(|&c| c == 1)
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

                let rhs = match sample_regex(regex, mngr.re_builder(), 100, !pol) {
                    Some(w) => w,
                    None => {
                        log::warn!("Could not sample from\n{}", regex);
                        return Some(subs); // short circuit here
                    }
                };

                if pol {
                    debug_assert!(
                        regex.accepts(&rhs),
                        "Regex: {} does not accept '{}'",
                        regex,
                        rhs
                    );
                } else {
                    debug_assert!(!regex.accepts(&rhs), "Regex: {} accepts '{}'", regex, rhs);
                }

                let rhs = mngr.const_string(rhs);
                subs.add(v.clone(), rhs);
                return Some(subs);
            }
            _ => (),
        }

        None
    }

    fn apply_atom(
        &self,
        atom: &Node,
        polarity: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution> {
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
                    return Some(subs);
                }
            }
            NodeKind::Eq => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();
                if let Some(subs) = self.try_reduce_eq(lhs, rhs, polarity, mngr) {
                    return Some(subs);
                }
            }
            NodeKind::InRe => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();

                if let NodeKind::Regex(re) = rhs.kind() {
                    if let Some(subs) = self.try_reduce_reg_membership(lhs, re, polarity, mngr) {
                        return Some(subs);
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
                                return Some(subs);
                            } else {
                                // abort here to not decent into the children
                                return Some(VarSubstitution::default());
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

impl EntailmentRule for IndependentVariableAssignment {
    fn apply(
        &self,
        node: &Node,
        _: &IndexSet<Node>,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution> {
        if node.is_atomic() {
            return self.apply_atom(node, pol, mngr);
        }
        None
    }

    fn init(&mut self, root: &Node, _: &mut NodeManager) {
        self.vcount.clear();
        Self::count_variables(root, &mut self.vcount);
    }
}
