mod regular;

use std::collections::HashSet;

use indexmap::IndexSet;
use regular::RegularBoundsInferer;

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, RegularConstraint, WordEquation},
};

use super::Bounds;

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

#[derive(Debug, Default)]
pub struct BoundInferer {
    reg: RegularBoundsInferer,
}

impl BoundInferer {
    fn add_reg(&mut self, reg: &RegularConstraint, pol: bool, ctx: &mut Context) {
        let v = reg
            .pattern()
            .as_variable()
            .expect("Regular constraints are only supported on variables.");
        let re = reg.re().clone();
        self.reg.add_reg(v, re, pol, ctx);
    }

    fn add_weq(&mut self, weq: &WordEquation, pol: bool, ctx: &mut Context) {
        match weq {
            WordEquation::ConstantEquality(_, _) => (),
            WordEquation::VarEquality(l, r) => {
                self.reg.add_var_eq(l.clone(), r.clone(), pol);
            }
            WordEquation::VarAssignment(l, r) => {
                self.reg.add_const_eq(l.clone(), r.clone(), pol, ctx);
            }
            WordEquation::General(_, _) => todo!("Support general word equations."),
        }
    }

    pub fn add_literal(&mut self, lit: Literal, ctx: &mut Context) {
        let pol = lit.polarity();
        match lit.atom().get_type() {
            AtomType::BoolVar(_) => (),
            AtomType::InRe(reg) => self.add_reg(reg, pol, ctx),
            AtomType::WordEquation(weq) => self.add_weq(weq, pol, ctx),
            AtomType::PrefixOf(_) | AtomType::SuffixOf(_) | AtomType::Contains(_) => {
                unreachable!("Formula not in normal form.")
            }
            AtomType::LinearConstraint(_) => {
                todo!("Support linear constraints.")
            }
        }
    }
}
