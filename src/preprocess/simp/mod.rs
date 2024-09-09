mod indep;
mod levis;
pub mod weq;

use indep::IndependentVarReducer;
use indexmap::IndexSet;

use crate::{
    context::Context,
    repr::ir::{Formula, Literal, VarSubstitution},
};

pub struct SimpResult {
    /// The simplified formula
    pub formula: Formula,
    /// The substitutions that were applied to the formula
    pub subst: VarSubstitution,
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
    pub fn simplify(&self, formula: Formula, ctx: &mut Context) -> SimpResult {
        let mut simplified = formula.clone();
        let mut applied_subst = VarSubstitution::default();

        let mut iterations = 0;
        let mut applied = true;

        while iterations < self.max_iterations && applied {
            simplified = simplified.reduce();
            applied = false;
            iterations += 1;

            // Apply the pure simplifications
            simplified = match self.apply_pure_simps(&simplified, true, &self.pure_simps(), ctx) {
                Some(simped) => {
                    applied = true;
                    simped
                }
                None => simplified,
            };

            // Apply the rewrite simplifications
            let simps = self.rewrite_simps(&simplified);
            let rewrites = self.infer_rewrite(&simplified, ctx, &simps);
            if !rewrites.is_empty() {
                applied_subst = applied_subst.compose(&rewrites);
                simplified = rewrites.apply(simplified, ctx);
                applied = true;
            }

            if applied {
                log::debug!(
                    "({}) Simpliefied to {} (using {})",
                    iterations,
                    simplified,
                    applied_subst
                );
            }
        }
        SimpResult {
            formula: simplified,
            subst: applied_subst,
        }
    }

    fn pure_simps(&self) -> Vec<Box<dyn PureSimplifier>> {
        vec![]
    }

    fn rewrite_simps(&self, fm: &Formula) -> Vec<Box<dyn RewriteSimplifier>> {
        vec![Box::new(IndependentVarReducer::new(fm))]
    }

    fn apply_pure_simps(
        &self,
        fm: &Formula,
        entailed: bool,
        simps: &[Box<dyn PureSimplifier>],
        ctx: &mut Context,
    ) -> Option<Formula> {
        match &fm {
            Formula::True => None,
            Formula::False => None,
            Formula::Literal(l) => {
                let mut simplified = None;
                for simp in simps {
                    if let Some(simped) =
                        simp.simplify(simplified.as_ref().unwrap_or(&l), entailed, ctx)
                    {
                        simplified = Some(simped);
                    }
                }
                Some(Formula::Literal(simplified?))
            }
            Formula::And(fs) | Formula::Or(fs) => {
                let mut simplified = false;
                let mut new_fs = Vec::with_capacity(fs.len());
                let entailed = entailed && matches!(fm, Formula::And(_));
                for f in fs {
                    match self.apply_pure_simps(f, entailed, simps, ctx) {
                        Some(simped) => {
                            simplified = true;
                            new_fs.push(simped);
                        }
                        None => new_fs.push(f.clone()),
                    }
                }
                if simplified {
                    match fm {
                        Formula::And(_) => Some(Formula::And(new_fs)),
                        Formula::Or(_) => Some(Formula::Or(new_fs)),
                        _ => unreachable!(),
                    }
                } else {
                    None
                }
            }
        }
    }

    fn infer_rewrite(
        &self,
        fm: &Formula,
        ctx: &mut Context,
        simps: &[Box<dyn RewriteSimplifier>],
    ) -> VarSubstitution {
        let mut rewrites = VarSubstitution::default();
        let entailed: IndexSet<_> = fm.entailed_literals().collect();
        for lit in fm.literals() {
            for simp in simps {
                if let Some(subst) = simp.infer(lit, entailed.contains(lit), ctx) {
                    // Try to infer as much a possible in one go.
                    // If two simplifiers infer the same variable, the first one wins.
                    let old = rewrites.clone();
                    let overwrites = rewrites.extend(&subst);
                    if !overwrites.is_empty() {
                        rewrites = old;
                        break;
                    }
                }
            }
        }
        rewrites
    }

    // /// Finds equalities of the form `x = t` where `x` is a variable and `t` is a term, which are entailed by the formula.
    // /// Replace all occurrences of `x` with `t` in the formula.
    // fn apply_entailed_equalities(&self, fm: &Formula, ctx: &mut Context) -> SimpRule<Formula> {
    //     let mut subst = VarSubstitution::default();
    //     for e_lit in fm.entailed_literals().filter(|l| l.polarity()) {
    //         match e_lit.atom().get_type() {
    //             AtomType::WordEquation(WordEquation::VarAssignment(v, pat)) => {
    //                 subst.set_str(v.clone(), Pattern::constant(pat));
    //             }
    //             AtomType::LinearConstraint(lc) if lc.operator() == LinearOperator::Eq => {
    //                 if let Some(v) = lc.lhs().as_variable() {
    //                     subst.set_int(v.clone(), LinearArithTerm::from_const(lc.rhs()));
    //                 }
    //             }
    //             _ => (),
    //         }
    //     }
    //     if subst.is_empty() {
    //         SimpRule::Unchanged
    //     } else {
    //         // Apply substitution
    //         let applied = subst.apply(fm.clone(), ctx);
    //         SimpRule::Simplified(applied, subst)
    //     }
    // }
}

/// Pure simplifier takes a literals and return a simplified version of it.
/// The simplified literal must be equisatisfiable with the original literal and not have any side effects.
trait PureSimplifier {
    /// Simplify the formula, returning a simplified version of it.
    /// If the formula cannot be simplified, return `None`.
    fn simplify(&self, lit: &Literal, entailed: bool, ctx: &mut Context) -> Option<Literal>;
}

/// Rewrite simplifier take a literal and return a substitution that can be applied to the formula to simplify it.
/// After applying the substitution, the formula must be equisatisfiable with the original formula.
trait RewriteSimplifier {
    fn infer(&self, fm: &Literal, entailed: bool, ctx: &mut Context) -> Option<VarSubstitution>;
}
