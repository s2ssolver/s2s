mod regular;

use std::collections::HashSet;

use indexmap::IndexSet;
use regular::RegularBoundsInferer;

use crate::{
    context::Context,
    repr::{
        ir::{AtomType, LinearConstraint, Literal, RegularConstraint, WordEquation},
        Sort, Sorted, Variable,
    },
};

use super::{Bounds, Interval};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FragmentPart {
    REG,
    WEQ,
    LIN,
}

/// A fragment of the supported theory.
/// Consists of a sequence of [FragmentPart]s.
/// If a fragment contains a fragment part, then the set of literals contains literals of that type.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Fragment {
    parts: HashSet<FragmentPart>,
}

impl Fragment {
    pub fn reg(&mut self) {
        self.parts.insert(FragmentPart::REG);
    }

    pub fn weq(&mut self) {
        self.parts.insert(FragmentPart::WEQ);
    }

    pub fn lin(&mut self) {
        self.parts.insert(FragmentPart::LIN);
    }

    pub fn is(&self, part: FragmentPart) -> bool {
        self.parts.contains(&part)
    }

    pub fn is_reg(&self) -> bool {
        self.is(FragmentPart::REG)
    }

    pub fn is_weq(&self) -> bool {
        self.is(FragmentPart::WEQ)
    }

    pub fn is_lin(&self) -> bool {
        self.is(FragmentPart::LIN)
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }
}

#[derive(Debug, Default, Clone)]
pub struct BoundInferer {
    literals: IndexSet<Literal>,
    // set to true if literals contain a conflict, i.e., a literal and its negation
    conflict: bool,
    reg: RegularBoundsInferer,
    fragment: Fragment,

    /// Variables for which we cannot infer bounds
    /// If bounds are inferred for variables in this set, they are overwriten as unbounded.
    /// This is used if we encounter fragments that we cannot handle (yet).
    unbounded: IndexSet<Variable>,
}

impl BoundInferer {
    fn add_reg(&mut self, reg: &RegularConstraint, pol: bool, ctx: &mut Context) {
        let v = reg
            .pattern()
            .as_variable()
            .expect("Regular constraints are only supported on variables.");
        let re = reg.re().clone();
        self.reg.add_reg(v, re, pol, ctx);
        self.fragment.reg();
    }

    fn add_weq(&mut self, weq: &WordEquation, pol: bool, ctx: &mut Context) {
        match weq {
            WordEquation::ConstantEquality(_, _) => (),
            WordEquation::VarEquality(l, r) => {
                self.reg.add_var_eq(l.clone(), r.clone(), pol);
                self.fragment.reg();
            }
            WordEquation::VarAssignment(l, r) => {
                self.reg.add_const_eq(l.clone(), r.clone(), pol, ctx);
                self.fragment.reg();
            }
            WordEquation::General(_, _) => {
                weq.variables().iter().for_each(|v| {
                    self.unbounded.insert(v.clone());
                });
                self.fragment.weq();
            }
        }
    }

    fn add_linear_constraint(&mut self, lc: &LinearConstraint) {
        self.fragment.lin();
        for v in lc.variables() {
            self.unbounded.insert(v.clone());
        }
    }

    pub fn add_literal(&mut self, lit: Literal, ctx: &mut Context) {
        self.literals.insert(lit.clone());

        self.conflict |= self.literals.contains(&lit.inverse());

        if !self.conflict {
            // skip this if there is a conflict
            let pol = lit.polarity();
            match lit.atom().get_type() {
                AtomType::BoolVar(_) => (),
                AtomType::InRe(reg) => self.add_reg(reg, pol, ctx),
                AtomType::WordEquation(weq) => self.add_weq(weq, pol, ctx),
                AtomType::PrefixOf(_) | AtomType::SuffixOf(_) | AtomType::Contains(_) => {
                    unreachable!("Formula not in normal form.")
                }
                AtomType::LinearConstraint(lc) => self.add_linear_constraint(lc),
            }
        }
    }

    /// Returns true if the literals contain a conflict, i.e., a literal and its negation.
    pub fn conflicting(&self) -> bool {
        self.conflict
    }

    /// Infers the bounds of the variables in the literals.
    pub fn infer(&self) -> Option<Bounds> {
        if self.conflict {
            return None;
        }
        let fragment = (
            self.fragment.is_reg(),
            self.fragment.is_weq(),
            self.fragment.is_lin(),
        );
        let mut bounds = match fragment {
            (true, _, _) => self.reg.infer_bounds(),
            (false, false, false) | (false, false, true) => Some(Bounds::empty()),
            _ => None,
        };

        // Overwrite bounds for unbounded variables
        if let Some(bounds) = bounds.as_mut() {
            for v in &self.unbounded {
                match v.sort() {
                    Sort::Int => bounds.set(v.clone(), Interval::bounded_below(0)),
                    Sort::String => bounds.set(v.clone(), Interval::unbounded()),
                    _ => unreachable!(),
                };
            }
        }
        bounds
    }
}
