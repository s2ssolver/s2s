mod equation;

use crate::formula::{Atom, Formula, Predicate};

use self::equation::preprocess_word_equation;

#[derive(Debug, Clone)]
pub enum PreprocessingResult<T> {
    Unchanged,
    Changed(T),
    False,
    True,
}

impl<T> PreprocessingResult<T> {
    pub fn as_option(&self) -> Option<&T> {
        match self {
            PreprocessingResult::Unchanged => None,
            PreprocessingResult::Changed(c) => Some(c),
            PreprocessingResult::False => None,
            PreprocessingResult::True => None,
        }
    }

    /// Returns [self] if the option is [PreprocessingResult::Unchanged], [PreprocessingResult::False], or [PreprocessingResult::True], otherwise calls f with the wrapped value and returns the result.
    pub fn and_then<F: FnOnce(T) -> PreprocessingResult<T>>(self, f: F) -> PreprocessingResult<T> {
        match self {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => f(c),
            PreprocessingResult::False => PreprocessingResult::False,
            PreprocessingResult::True => PreprocessingResult::True,
        }
    }
}

fn preprocess_predicate(pred: &Predicate) -> PreprocessingResult<Predicate> {
    match pred {
        Predicate::WordEquation(weq) => match preprocess_word_equation(weq) {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => {
                PreprocessingResult::Changed(Predicate::WordEquation(c))
            }
            PreprocessingResult::False => PreprocessingResult::False,
            PreprocessingResult::True => PreprocessingResult::True,
        },
        Predicate::RegularConstraint(_, _) => PreprocessingResult::Unchanged,
        Predicate::LinearConstraint(_) => PreprocessingResult::Unchanged,
    }
}

/* Todo: Activate/Deactivate preprocessing steps using structs of traits {Formula Preprocessor, Predicate Preprocessor}
 * Todo: Add more preprocessing steps:
 * - Collapse nested And/Or
 * - Remove duplicate atoms from And/Or
 * - Collapse double negation
 * - Convert to nnf
 */
/// Preprocesses the given formula
pub fn preprocess(formula: &Formula) -> PreprocessingResult<Formula> {
    match formula {
        Formula::Atom(a) => match a {
            Atom::Predicate(p) => match preprocess_predicate(p) {
                PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
                PreprocessingResult::Changed(c) => {
                    PreprocessingResult::Changed(Formula::Atom(Atom::Predicate(c)))
                }
                PreprocessingResult::False => PreprocessingResult::False,
                PreprocessingResult::True => PreprocessingResult::True,
            },
            _ => PreprocessingResult::Unchanged,
        },
        Formula::Or(fs) => {
            let mut preprocessed_fs = Vec::new();
            let mut unchanged = true;
            for f in fs {
                match preprocess(f) {
                    PreprocessingResult::Unchanged => preprocessed_fs.push(f.clone()),
                    PreprocessingResult::Changed(c) => {
                        unchanged = false;
                        preprocessed_fs.push(c);
                    }
                    PreprocessingResult::False => return PreprocessingResult::False,
                    PreprocessingResult::True => {
                        // Ignore true
                    }
                }
            }
            if unchanged {
                PreprocessingResult::Unchanged
            } else {
                PreprocessingResult::Changed(Formula::or(preprocessed_fs))
            }
        }
        Formula::And(fs) => {
            let mut preprocessed_fs = Vec::new();
            let mut unchanged = true;
            for f in fs {
                match preprocess(f) {
                    PreprocessingResult::Unchanged => preprocessed_fs.push(f.clone()),
                    PreprocessingResult::Changed(c) => {
                        unchanged = false;
                        preprocessed_fs.push(c);
                    }
                    PreprocessingResult::False => return PreprocessingResult::False,
                    PreprocessingResult::True => {
                        // Ignore true
                    }
                }
            }
            if unchanged {
                PreprocessingResult::Unchanged
            } else {
                PreprocessingResult::Changed(Formula::and(preprocessed_fs))
            }
        }
        Formula::Not(f) => match preprocess(f) {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => PreprocessingResult::Changed(Formula::not(c)),
            PreprocessingResult::False => PreprocessingResult::True,
            PreprocessingResult::True => PreprocessingResult::False,
        },
    }
}
