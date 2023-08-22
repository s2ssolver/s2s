//! Preprocessors for formulas

use crate::{
    instance::Instance,
    model::{
        formula::{Formula, NNFFormula},
        Evaluable, Substitution,
    },
    preprocess::Preprocessor,
    PreprocessingResult,
};

/// Simplifies conjunctions of formulas:
/// - `true ∧ f` is simplified to `f`
/// - `false ∧ f` is simplified to `false`
pub struct ConjunctionSimplifier {}

impl Preprocessor for ConjunctionSimplifier {
    fn get_substitution(&self) -> Option<Substitution> {
        None
    }

    fn get_name(&self) -> String {
        String::from("Conjunction simplifier")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }

    fn apply_fm(
        &mut self,
        formula: NNFFormula,
        _is_asserted: bool,
        _instance: &mut Instance,
    ) -> PreprocessingResult {
        match formula {
            NNFFormula::Literal(_) => PreprocessingResult::Unchanged(formula),
            NNFFormula::Or(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    let pf = match self.apply_fm(f, _is_asserted, _instance) {
                        PreprocessingResult::Unchanged(f) => f,
                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            f
                        }
                    };
                    match pf.eval(&Substitution::new()) {
                        Some(true) => {
                            return PreprocessingResult::Changed(Formula::ttrue().into());
                        }
                        Some(false) => (),
                        None => {
                            new_fs.push(pf);
                        }
                    }
                }
                let new_fm = NNFFormula::Or(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
            NNFFormula::And(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    let pf = match self.apply_fm(f, _is_asserted, _instance) {
                        PreprocessingResult::Unchanged(f) => f,

                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            f
                        }
                    };
                    match pf.eval(&Substitution::new()) {
                        Some(true) => (),
                        Some(false) => {
                            return PreprocessingResult::Changed(Formula::ffalse().into());
                        }
                        None => {
                            new_fs.push(pf);
                        }
                    }
                }
                let new_fm = NNFFormula::And(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
        }
    }
}
