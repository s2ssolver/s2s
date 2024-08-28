mod indep;
mod weq;

use crate::{
    context::Context,
    repr::ir::{
        AtomType, Formula, LinearArithTerm, LinearOperator, Literal, Pattern, VarSubstitution,
        WordEquation,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimplificationResult<T> {
    Simplified(T, VarSubstitution),
    Trivial(bool),
    Unchanged,
}

const DEFAULT_MAX_ITERATIONS: usize = 20;

pub struct Simplifier {
    max_iterations: usize,
}
impl Default for Simplifier {
    fn default() -> Self {
        Self {
            max_iterations: DEFAULT_MAX_ITERATIONS,
        }
    }
}

impl Simplifier {
    pub fn simplify(&self, formula: Formula, ctx: &mut Context) -> SimplificationResult<Formula> {
        let mut simplified = formula.clone();
        let mut subst = VarSubstitution::default();
        let mut iterations = 0;
        let mut applied = true;

        while iterations < self.max_iterations && applied {
            simplified = simplified.reduce();
            applied = false;
            iterations += 1;

            // These are recreated in each iteration, because they might depend on the current formula
            let simps = self.build_simps(&simplified);

            // Apply all literal simplifications
            match self.simp_lits(&simplified, ctx, &simps) {
                SimplificationResult::Simplified(simped, new_subs) => {
                    simplified = simped;
                    subst = subst.compose(&new_subs);
                    applied = true;
                }
                SimplificationResult::Trivial(b) => return SimplificationResult::Trivial(b),
                SimplificationResult::Unchanged => {}
            }
            log::debug!("Round {}: {}", iterations, simplified);
        }
        SimplificationResult::Simplified(simplified, subst)
    }

    fn build_simps(&self, fm: &Formula) -> Vec<Box<dyn LiteralSimplifier>> {
        vec![Box::new(indep::IndependentVarReducer::new(fm))]
    }

    fn simp_lits(
        &self,
        formula: &Formula,
        ctx: &mut Context,
        simps: &[Box<dyn LiteralSimplifier>],
    ) -> SimplificationResult<Formula> {
        match formula {
            Formula::True | Formula::False => SimplificationResult::Unchanged,
            Formula::Literal(l) => {
                let mut applied = false;
                let mut simped = l.clone();
                let mut subs = VarSubstitution::default();
                for simp in simps.iter() {
                    match simp.simplify(&simped, ctx) {
                        SimplificationResult::Simplified(simped_lit, new_subs) => {
                            subs = subs.compose(&new_subs);
                            simped = simped_lit;
                            applied = true;
                        }
                        SimplificationResult::Trivial(t) => {
                            return SimplificationResult::Trivial(t)
                        }
                        SimplificationResult::Unchanged => (),
                    }
                }
                if applied {
                    SimplificationResult::Simplified(Formula::Literal(simped), subs)
                } else {
                    SimplificationResult::Unchanged
                }
            }
            Formula::And(fs) | Formula::Or(fs) => {
                let mut applied = false;
                let mut simped = Vec::with_capacity(fs.len());
                let mut subs = VarSubstitution::default();
                for f in fs.iter() {
                    match self.simp_lits(f, ctx, simps) {
                        SimplificationResult::Simplified(f, subst) => {
                            simped.push(f);
                            subs = subs.compose(&subst);
                            applied = true;
                        }
                        SimplificationResult::Trivial(t) => {
                            return SimplificationResult::Trivial(t)
                        }
                        SimplificationResult::Unchanged => simped.push(f.clone()),
                    }
                }
                if applied {
                    match formula {
                        Formula::And(_) => {
                            SimplificationResult::Simplified(Formula::And(simped), subs)
                        }
                        Formula::Or(_) => {
                            SimplificationResult::Simplified(Formula::Or(simped), subs)
                        }
                        _ => unreachable!(),
                    }
                } else {
                    SimplificationResult::Unchanged
                }
            }
        }
    }

    /// Finds equalities of the form `x = t` where `x` is a variable and `t` is a term, which are entailed by the formula.
    /// Replace all occurrences of `x` with `t` in the formula.
    fn apply_entailed_equalities(
        &self,
        fm: &Formula,
        ctx: &mut Context,
    ) -> SimplificationResult<Formula> {
        let mut subst = VarSubstitution::default();
        for e_lit in fm.entailed_literals().filter(|l| l.polarity()) {
            match e_lit.atom().get_type() {
                AtomType::WordEquation(WordEquation::VarAssignment(v, pat)) => {
                    subst.set_str(v.clone(), Pattern::constant(pat));
                }
                AtomType::LinearConstraint(lc) if lc.typ() == LinearOperator::Eq => {
                    if let Some(v) = lc.lhs().as_variable() {
                        subst.set_int(v.clone(), LinearArithTerm::from_const(lc.rhs()));
                    }
                }
                _ => (),
            }
        }
        if subst.is_empty() {
            SimplificationResult::Unchanged
        } else {
            // Apply substitution
            let applied = subst.apply(fm.clone(), ctx);
            SimplificationResult::Simplified(applied, subst)
        }
    }
}

pub trait LiteralSimplifier {
    fn simplify(&self, lit: &Literal, ctx: &mut Context) -> SimplificationResult<Literal>;
}
