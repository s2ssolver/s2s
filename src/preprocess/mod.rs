mod equation;

use std::fmt::Display;

use crate::{
    model::formula::{Formula, Predicate},
    parse::Instance,
};

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
    pub fn and_then_or<F: FnOnce(&T) -> PreprocessingResult<T>>(
        self,
        f: F,
        default: &T,
    ) -> PreprocessingResult<T> {
        match self {
            PreprocessingResult::Unchanged => f(default),
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
    todo!("Preprocess predicate {}", pred)
}

/* Todo: Activate/Deactivate preprocessing steps using structs of traits {Formula Preprocessor, Predicate Preprocessor}
 * Todo: Add more preprocessing steps:
 * - Collapse nested And/Or
 * - Remove duplicate atoms from And/Or
 * - Collapse double negation
 * - Convert to nnf
 */
/// Preprocesses the given formula
fn preprocess_formula(formula: &Formula) -> PreprocessingResult<Formula> {
    todo!("Preprocess formula {}", formula)
}

pub fn preprocess(instance: &Instance) -> PreprocessingResult<Formula> {
    todo!("Preprocess instance {:?}", instance)
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
