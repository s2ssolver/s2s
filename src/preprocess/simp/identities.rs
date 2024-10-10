use regulaer::re::RegOp;

use crate::{
    context::Context,
    ir::{
        AtomType, LinearArithTerm, LinearOperator, Literal, Pattern, Symbol, VarSubstitution,
        WordEquation,
    },
};

use super::{RewriteSimplifier, Simplifier};

/// Finds equalities of the form `x = t` where `x` is a variable and `t` is a term, which are entailed by the formula.
pub struct EntailedIdentities;
impl Simplifier for EntailedIdentities {
    fn name(&self) -> &'static str {
        "EntailedIdentities"
    }
}
impl RewriteSimplifier for EntailedIdentities {
    fn infer(&self, lit: &Literal, entailed: bool, _ctx: &mut Context) -> Option<VarSubstitution> {
        if lit.polarity() && entailed {
            match lit.atom().get_type() {
                AtomType::WordEquation(weq) => match weq {
                    WordEquation::VarEquality(v1, v2) => {
                        let mut subst = VarSubstitution::default();
                        // v1 |-> v2
                        subst.set_str(v1.clone(), Pattern::variable(v2));
                        Some(subst)
                    }
                    WordEquation::VarAssignment(v, c) => {
                        let mut subst = VarSubstitution::default();
                        // v |-> c
                        subst.set_str(v.clone(), Pattern::constant(c));
                        Some(subst)
                    }
                    WordEquation::General(l, r) => {
                        let mut subst = VarSubstitution::default();
                        if let Some(v) = l.as_variable() {
                            // v |-> r
                            subst.set_str(v.clone(), r.clone());
                            Some(subst)
                        } else if let Some(v) = r.as_variable() {
                            // v |-> l
                            subst.set_str(v.clone(), l.clone());
                            Some(subst)
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
                AtomType::LinearConstraint(lc) if lc.operator() == LinearOperator::Eq => {
                    let v = lc.lhs().as_variable()?;
                    let mut subst = VarSubstitution::default();
                    subst.set_int(v.clone(), LinearArithTerm::from_const(lc.rhs()));
                    Some(subst)
                }
                AtomType::InRe(inre) => {
                    let v = inre.pattern().as_variable()?;
                    if let RegOp::Const(w) = inre.re().op() {
                        let mut subst = VarSubstitution::default();
                        let mut pattern = Pattern::empty();
                        for c in w.iter() {
                            pattern.push(Symbol::Constant(c))
                        }
                        subst.set_str(v.clone(), pattern);
                        Some(subst)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }
}
