//! Preprocessors for formulas

use crate::{
    model::{formula::Formula, Evaluable, Substitution},
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

    fn apply_fm(&mut self, formula: Formula, _is_asserted: bool) -> PreprocessingResult {
        match formula {
            Formula::Atom(_) => PreprocessingResult::Unchanged(formula),
            Formula::Or(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    match self.apply_fm(f, _is_asserted) {
                        PreprocessingResult::Unchanged(f) => new_fs.push(f),
                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            new_fs.push(f);
                        }
                    }
                }
                let new_fm = Formula::or(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
            Formula::And(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    let pf = match self.apply_fm(f, _is_asserted) {
                        PreprocessingResult::Unchanged(f) => f,

                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            f
                        }
                    };
                    match pf.eval(&Substitution::new()) {
                        Some(true) => (),
                        Some(false) => return PreprocessingResult::Changed(Formula::ffalse()),
                        None => {
                            new_fs.push(pf);
                            changed = true;
                        }
                    }
                }
                let new_fm = Formula::and(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
            Formula::Not(f) => match self.apply_fm(*f, _is_asserted) {
                PreprocessingResult::Unchanged(f) => {
                    PreprocessingResult::Unchanged(Formula::not(f))
                }
                PreprocessingResult::Changed(f) => PreprocessingResult::Changed(Formula::not(f)),
            },
        }
    }
}
