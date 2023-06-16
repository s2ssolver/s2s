//! Preprocessor for the `int` type.

use crate::{
    model::{
        formula::{Formula, Predicate, Term},
        Substitution,
    },
    preprocess::Preprocessor,
    PreprocessingResult,
};

/// Reduces constant integer expressions.
#[derive(Debug, Default)]
pub struct ConstIntReducer {}

impl Preprocessor for ConstIntReducer {
    fn get_substitution(&self) -> Option<Substitution> {
        None
    }

    fn get_name(&self) -> String {
        String::from("Integer constant reduction")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self::default()
    }

    fn apply_predicate(&mut self, predicate: Predicate, _is_asserted: bool) -> PreprocessingResult {
        match predicate {
            Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l == r {
                            PreprocessingResult::Changed(Formula::True)
                        } else {
                            PreprocessingResult::Changed(Formula::False)
                        }
                    }
                    _ => {
                        return PreprocessingResult::Unchanged(Formula::predicate(
                            Predicate::Equality(lhs.into(), rhs.into()),
                        ))
                    }
                }
            }
            Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l >= r {
                            PreprocessingResult::Changed(Formula::True)
                        } else {
                            PreprocessingResult::Changed(Formula::False)
                        }
                    }
                    _ => {
                        return PreprocessingResult::Unchanged(Formula::predicate(Predicate::Geq(
                            lhs.into(),
                            rhs.into(),
                        )))
                    }
                }
            }
            Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l > r {
                            PreprocessingResult::Changed(Formula::True)
                        } else {
                            PreprocessingResult::Changed(Formula::False)
                        }
                    }
                    _ => {
                        return PreprocessingResult::Unchanged(Formula::predicate(
                            Predicate::Greater(lhs.into(), rhs.into()),
                        ))
                    }
                }
            }
            Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l <= r {
                            PreprocessingResult::Changed(Formula::True)
                        } else {
                            PreprocessingResult::Changed(Formula::False)
                        }
                    }
                    _ => {
                        return PreprocessingResult::Unchanged(Formula::predicate(Predicate::Leq(
                            lhs.into(),
                            rhs.into(),
                        )))
                    }
                }
            }
            Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l < r {
                            PreprocessingResult::Changed(Formula::True)
                        } else {
                            PreprocessingResult::Changed(Formula::False)
                        }
                    }
                    _ => {
                        return PreprocessingResult::Unchanged(Formula::predicate(Predicate::Less(
                            lhs.into(),
                            rhs.into(),
                        )))
                    }
                }
            }
            _ => return PreprocessingResult::Unchanged(Formula::predicate(predicate)),
        }
    }
}
