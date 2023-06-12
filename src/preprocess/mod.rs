mod equation;

use std::fmt::Display;

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

    /// Maps [PreprocessingResult::Changed] using the given function, otherwise returns [self].
    pub fn map<F: FnOnce(T) -> T>(self, f: F) -> PreprocessingResult<T> {
        match self {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => PreprocessingResult::Changed(f(c)),
            PreprocessingResult::False => PreprocessingResult::False,
            PreprocessingResult::True => PreprocessingResult::True,
        }
    }

    /// Returns [self] if the option is [PreprocessingResult::Unchanged], [PreprocessingResult::False], or [PreprocessingResult::True], otherwise calls f with the wrapped value and returns the result.
    /// If f returns [PreprocessingResult::Unchanged], returns [self].
    pub fn and_then<F: FnOnce(&T) -> PreprocessingResult<T>>(self, f: F) -> PreprocessingResult<T> {
        match self {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => {
                let next = f(&c);
                match next {
                    PreprocessingResult::Unchanged => PreprocessingResult::Changed(c),
                    PreprocessingResult::Changed(cc) => PreprocessingResult::Changed(cc),
                    PreprocessingResult::False => PreprocessingResult::False,
                    PreprocessingResult::True => PreprocessingResult::True,
                }
            }
            PreprocessingResult::False => PreprocessingResult::False,
            PreprocessingResult::True => PreprocessingResult::True,
        }
    }

    /// If is [PreprocessingResult::Changed], returns the contained value, otherwise returns the provided default.
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            PreprocessingResult::Unchanged => default,
            PreprocessingResult::Changed(c) => c,
            PreprocessingResult::False => default,
            PreprocessingResult::True => default,
        }
    }
}

fn preprocess_predicate(pred: &Predicate) -> PreprocessingResult<Predicate> {
    log::trace!("Preprocessing Predicate {}", pred);
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
pub fn preprocess_formula(formula: &Formula) -> PreprocessingResult<Formula> {
    log::trace!("Preprocessing Formula {}", formula);
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
                match preprocess_formula(f) {
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
                match preprocess_formula(f) {
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
        Formula::Not(f) => match preprocess_formula(f) {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => PreprocessingResult::Changed(Formula::not(c)),
            PreprocessingResult::False => PreprocessingResult::True,
            PreprocessingResult::True => PreprocessingResult::False,
        },
    }
}

pub fn preprocess(formula: &Formula) -> PreprocessingResult<Formula> {
    // Apply preprocessing steps
    let mut preprocessed = preprocess_formula(formula);

    // Deduce substitutions

    preprocessed
}

impl<T: Display> Display for PreprocessingResult<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreprocessingResult::Unchanged => write!(f, "Unchanged"),
            PreprocessingResult::Changed(c) => write!(f, "Changed to {}", c),
            PreprocessingResult::False => write!(f, "False"),
            PreprocessingResult::True => write!(f, "True"),
        }
    }
}
