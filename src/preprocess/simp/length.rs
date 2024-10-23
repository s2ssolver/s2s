use crate::{
    context::Context,
    ir::{AtomType, LinearOperator, LinearSummand, Literal, Pattern, VarSubstitution},
};

use super::{RewriteSimplifier, Simplifier};

/// Finds asserted terms of the form `L = 0` or `L <= 0`, where
/// all terms in L are of the form c|x| with c>0
/// and returns `x = epsilon` for all c|x| in L.`
pub struct ZeroLengthEpsilon;

impl Simplifier for ZeroLengthEpsilon {
    fn name(&self) -> &'static str {
        "zero_length_epsilon"
    }
}
impl RewriteSimplifier for ZeroLengthEpsilon {
    fn infer(&self, lit: &Literal, entailed: bool, _: &mut Context) -> Option<VarSubstitution> {
        if lit.polarity() && entailed {
            if let AtomType::LinearConstraint(lc) = lit.atom().get_type() {
                if (lc.operator() == LinearOperator::Eq || lc.operator() == LinearOperator::Leq)
                    && lc.rhs() == 0
                {
                    let mut vars = vec![];
                    for summand in lc.lhs().iter() {
                        if let LinearSummand::Mult(v, c) = summand {
                            if v.is_len() && *c > 0 {
                                vars.push(v.variable().clone());
                            } else {
                                return None;
                            }
                        } else {
                            return None;
                        }
                    }
                    let mut subs = VarSubstitution::default();
                    for v in vars {
                        subs.set_str(v, Pattern::empty());
                    }
                    return Some(subs);
                }
            }
        }
        return None;
    }
}
