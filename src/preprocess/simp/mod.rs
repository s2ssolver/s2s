mod identities;
mod indep;
mod levis;
mod regex;
mod substring;
pub mod weq;

use indep::IndependentVarReducer;
use indexmap::IndexSet;

use crate::{
    context::Context,
    ir::{Formula, Literal, VarSubstitution},
};

pub struct SimpResult {
    /// The simplified formula
    pub formula: Formula,
    /// The substitutions that were applied to the formula
    pub subst: VarSubstitution,
}

pub fn simplify(formula: Formula, ctx: &mut Context, max_iters: usize) -> SimpResult {
    let mut simplified = formula.clone();
    let mut applied_subst = VarSubstitution::default();

    let mut iterations = 0;
    let mut applied = true;

    while iterations < max_iters && applied {
        simplified = simplified.reduce();
        log::debug!("Trivally reduced to {}", simplified);
        applied = false;
        iterations += 1;

        // Apply the pure simplifications
        simplified = match apply_pure_simps(&simplified, true, &pure_simps(), ctx) {
            Some(simped) => {
                applied = true;
                simped
            }
            None => simplified,
        };

        // Apply the rewrite simplifications
        let simps = rewrite_simps(&simplified);
        if let Some(rewrite) = infer_rewrite(&simplified, ctx, &simps) {
            simplified = rewrite.apply(simplified, ctx);
            applied_subst = applied_subst.compose(&rewrite);
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
    // Need to reduce one more time to ensure that the formula does not contain any constant literals which cannot be encoded
    simplified = simplified.reduce();
    log::debug!("Trivally reduced to {}", simplified);
    SimpResult {
        formula: simplified,
        subst: applied_subst,
    }
}

fn pure_simps() -> Vec<Box<dyn PureSimplifier>> {
    vec![
        Box::new(weq::StripCommonPrefixSuffix),
        Box::new(regex::ConstantDerivation),
    ]
}

fn rewrite_simps(fm: &Formula) -> Vec<Box<dyn RewriteSimplifier>> {
    vec![
        Box::new(identities::EntailedIdentities),
        Box::new(IndependentVarReducer::new(fm)),
        Box::new(substring::ConstantPrefixSuffix),
        Box::new(regex::ConstantPrefixSuffix),
        Box::new(levis::LevisSimp),
    ]
}

fn apply_pure_simps(
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
                    log::debug!(
                        "[{}] Simplified {} to {}",
                        simp.name(),
                        simplified.as_ref().unwrap_or(&l),
                        simped
                    );
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
                match apply_pure_simps(f, entailed, simps, ctx) {
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
    fm: &Formula,
    ctx: &mut Context,
    simps: &[Box<dyn RewriteSimplifier>],
) -> Option<VarSubstitution> {
    let entailed: IndexSet<_> = fm.entailed_literals().collect();
    for lit in fm.literals() {
        for simp in simps {
            if let Some(subst) = simp.infer(lit, entailed.contains(lit), ctx) {
                log::debug!(
                    "[{}] Inferred substitution {} from {}",
                    simp.name(),
                    subst,
                    lit
                );
                return Some(subst);
            }
        }
    }
    None
}

trait Simplifier {
    fn name(&self) -> &'static str;
}

/// Pure simplifier takes a literals and return a simplified version of it.
/// The simplified literal must be equisatisfiable with the original literal and not have any side effects.
trait PureSimplifier: Simplifier {
    /// Simplify the formula, returning a simplified version of it.
    /// If the formula cannot be simplified, return `None`.
    fn simplify(&self, lit: &Literal, entailed: bool, ctx: &mut Context) -> Option<Literal>;
}

/// Rewrite simplifier take a literal and return a substitution that can be applied to the formula to simplify it.
/// After applying the substitution, the formula must be equisatisfiable with the original formula.
trait RewriteSimplifier: Simplifier {
    fn infer(&self, lit: &Literal, entailed: bool, ctx: &mut Context) -> Option<VarSubstitution>;
}
