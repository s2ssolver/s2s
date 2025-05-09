//! Simplification for variables the occur only once in the formula.

use std::rc::Rc;

use smt_str::sampling::sample_nfa;
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
        ctx: &mut Context,
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
                            ctx.ast().const_str("a")
                        } else {
                            ctx.ast().empty_string()
                        };
                        subs.add(v.clone(), rhs);
                        Some(subs)
                    }
                    NodeKind::Int(i) => {
                        let mut subs = VarSubstitution::default();
                        let rhs = if pol {
                            rhs.clone()
                        } else if *i != 0 {
                            ctx.ast().const_int(0)
                        } else {
                            ctx.ast().const_int(1)
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
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        match lhs.kind() {
            NodeKind::Variable(v) if self.independent(v) => {
                let mut subs = VarSubstitution::default();
                let rhs = match sample_regex(regex, ctx.re_builder(), 1000, !pol) {
                    smt_str::sampling::SampleResult::Sampled(s) => s,
                    _ => {
                        // Fallback: sample from NFA
                        log::debug!(
                            "Could not sample from regex directly, falling back to NFA sampling"
                        );
                        let nfa = ctx.get_nfa(regex);
                        match sample_nfa(&nfa, 1000, !pol) {
                            smt_str::sampling::SampleResult::Sampled(s) => s,
                            _ => {
                                log::debug!("Could not sample from {}", regex);
                                return None;
                            }
                        }
                    }
                };

                let ok = if pol {
                    regex.accepts(&rhs)
                } else {
                    !regex.accepts(&rhs)
                };
                debug_assert!(ok, "Sample invalid word '{}' for ({}) '{}' ", rhs, pol, rhs);
                if !ok {
                    log::warn!("Sample invalid word '{}' for ({}) '{}' ", rhs, pol, rhs);
                    return None;
                }

                let rhs = ctx.ast().const_string(rhs);
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
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        debug_assert!(atom.is_atomic(), "{} is not an atomic formula", atom);
        match atom.kind() {
            NodeKind::Variable(v) => {
                let mut subs = VarSubstitution::default();
                if self.independent(v) {
                    if polarity {
                        subs.add(v.clone(), ctx.ast().ttrue());
                    } else {
                        subs.add(v.clone(), ctx.ast().ffalse());
                    }
                    return Some(subs);
                }
            }
            NodeKind::Eq => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();
                if let Some(subs) = self.try_reduce_eq(lhs, rhs, polarity, ctx) {
                    return Some(subs);
                }
            }
            NodeKind::InRe => {
                let lhs = atom.children().first().unwrap();
                let rhs = atom.children().last().unwrap();

                if let NodeKind::Regex(re) = rhs.kind() {
                    if let Some(subs) = self.try_reduce_reg_membership(lhs, re, polarity, ctx) {
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
                                let rhs = ctx.ast().const_string(asstr.clone());
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
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        if node.is_atomic() {
            return self.apply_atom(node, pol, ctx);
        }
        None
    }

    fn init(&mut self, root: &Node, _: &mut Context) {
        self.vcount.clear();
        Self::count_variables(root, &mut self.vcount);
    }
}
