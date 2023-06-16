mod string;

use std::fmt::Display;

use crate::{
    model::{formula::Formula, Substitutable, Substitution},
    parse::Instance,
};

#[derive(Debug, Clone)]
pub enum PreprocessingResult {
    Changed(Formula),
    Unchanged,
}

impl PreprocessingResult {
    const fn as_ref(&self) -> Option<&Formula> {
        match self {
            PreprocessingResult::Unchanged => None,
            PreprocessingResult::Changed(c) => Some(c),
        }
    }

    fn is_unchanged(&self) -> bool {
        match self {
            PreprocessingResult::Unchanged => true,
            PreprocessingResult::Changed(_) => false,
        }
    }
}

impl From<Option<Formula>> for PreprocessingResult {
    fn from(f: Option<Formula>) -> Self {
        match f {
            None => PreprocessingResult::Unchanged,
            Some(f) => PreprocessingResult::Changed(f),
        }
    }
}

trait Preprocessor {
    fn preprocess(&self, pred: &Formula) -> PreprocessingResult;

    fn preprocess_asserted(&self, pred: &Formula, sub: &mut Substitution) -> PreprocessingResult {
        self.preprocess(pred)
    }
}

/// Applies the given preprocessors to the given formula and returns the result.
fn apply_preprocessors(
    formula: &Formula,
    preprocessors: &Vec<Box<dyn Preprocessor>>,
    sub: &mut Substitution,
    is_asserted: bool,
) -> PreprocessingResult {
    let mut current = PreprocessingResult::Unchanged;
    for processor in preprocessors {
        let f = match current.as_ref() {
            None => formula,
            Some(f) => f,
        };
        let result = if is_asserted {
            processor.preprocess_asserted(f, sub)
        } else {
            processor.preprocess(f)
        };
        match result {
            PreprocessingResult::Unchanged => continue,
            PreprocessingResult::Changed(c) => current = PreprocessingResult::Changed(c),
        }
    }
    current
}

fn preprocess_formula(
    formula: &Formula,
    preprocessors: &Vec<Box<dyn Preprocessor>>,
    sub: &mut Substitution,
    is_asserted: bool,
) -> PreprocessingResult {
    match formula {
        Formula::True => PreprocessingResult::Unchanged,
        Formula::False => PreprocessingResult::Unchanged,
        Formula::BoolVar(_) | Formula::Predicate(_) => {
            apply_preprocessors(formula, preprocessors, sub, is_asserted)
        }
        Formula::Or(fs) => {
            // Apply preprocessors to all subformulas
            let mut preprocessed = fs
                .iter()
                .enumerate()
                .map(|(i, f)| (i, apply_preprocessors(f, preprocessors, sub, false)));
            if preprocessed.all(|(_, p)| p.is_unchanged()) {
                // Apply preprocessors to the original formula
                apply_preprocessors(formula, preprocessors, sub, is_asserted)
            } else {
                let mut new_fs = Vec::new();
                for (i, p) in preprocessed {
                    match p {
                        PreprocessingResult::Unchanged => new_fs.push(fs[i].clone()),
                        PreprocessingResult::Changed(c) => new_fs.push(c),
                    }
                }
                // Apply preprocessors to the preprocessed formula
                apply_preprocessors(&Formula::or(new_fs), preprocessors, sub, is_asserted)
            }
        }
        Formula::And(fs) => {
            // Apply preprocessors to all subformulas
            let mut preprocessed = fs
                .iter()
                .enumerate()
                .map(|(i, f)| (i, apply_preprocessors(f, preprocessors, sub, is_asserted)));
            if preprocessed.all(|(_, p)| p.is_unchanged()) {
                // Apply preprocessors to the original formula
                apply_preprocessors(formula, preprocessors, sub, is_asserted)
            } else {
                let mut new_fs = Vec::new();
                for (i, p) in preprocessed {
                    match p {
                        PreprocessingResult::Unchanged => new_fs.push(fs[i].clone()),
                        PreprocessingResult::Changed(c) => new_fs.push(c),
                    }
                }
                // Apply preprocessors to the preprocessed formula
                apply_preprocessors(&Formula::and(new_fs), preprocessors, sub, is_asserted)
            }
        }
        Formula::Not(f) => {
            // Apply preprocessors to the subformula
            let preprocessed = apply_preprocessors(f, preprocessors, sub, true);
            match preprocessed {
                PreprocessingResult::Unchanged => {
                    apply_preprocessors(formula, preprocessors, sub, is_asserted)
                }
                PreprocessingResult::Changed(c) => {
                    apply_preprocessors(&Formula::not(c), preprocessors, sub, is_asserted)
                }
            }
        }
    }
}

pub fn preprocess(instance: &Instance) -> PreprocessingResult {
    let mut sub = Substitution::new();
    let mut preprocessors: Vec<Box<dyn Preprocessor>> = Vec::new();
    let max_rounds = 10;
    let mut result = None;
    for r in 0..max_rounds {
        let formula = match result.as_ref() {
            None => instance.get_formula(),
            Some(f) => f,
        };
        let mut preprocessed = preprocess_formula(formula, &preprocessors, &mut sub, true);

        // Apply the inferred substitution to the preprocessed formula
        preprocessed = match preprocessed {
            PreprocessingResult::Changed(c) => {
                // Apply substitutions to the preprocessed formula
                if sub.is_empty() {
                    PreprocessingResult::Changed(c)
                } else {
                    let applied = c.apply_substitution(&sub);
                    PreprocessingResult::Changed(applied)
                }
            }
            PreprocessingResult::Unchanged => {
                // Apply substitution to the formula
                if sub.is_empty() {
                    PreprocessingResult::Unchanged
                } else {
                    let applied = instance.get_formula().apply_substitution(&sub);
                    PreprocessingResult::Changed(applied)
                }
            }
        };

        match preprocessed {
            PreprocessingResult::Unchanged => {
                break;
            }
            PreprocessingResult::Changed(c) => {
                log::debug!("Preprocessing round {} done.", r);
                result = Some(c);
            }
        }
    }
    match result {
        None => PreprocessingResult::Unchanged,
        Some(f) => PreprocessingResult::Changed(f),
    }
}

impl Display for PreprocessingResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreprocessingResult::Unchanged => write!(f, "Unchanged"),
            PreprocessingResult::Changed(c) => write!(f, "Changed to {}", c),
        }
    }
}
