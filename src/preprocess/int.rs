//! Preprocessor for the `int` type.

use crate::{
    model::{
        formula::{Formula, Predicate},
        terms::{IntTerm, Term},
        Substitution,
    },
    preprocess::Preprocessor,
    PreprocessingResult,
};

/// Reduces constant integer predicates to `true` or `false`
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
                            PreprocessingResult::Changed(Formula::ttrue())
                        } else {
                            PreprocessingResult::Changed(Formula::ffalse())
                        }
                    }
                    _ => PreprocessingResult::Unchanged(Formula::predicate(Predicate::Equality(
                        lhs.into(),
                        rhs.into(),
                    ))),
                }
            }
            Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l >= r {
                            PreprocessingResult::Changed(Formula::ttrue())
                        } else {
                            PreprocessingResult::Changed(Formula::ffalse())
                        }
                    }
                    _ => PreprocessingResult::Unchanged(Formula::predicate(Predicate::Geq(
                        lhs.into(),
                        rhs.into(),
                    ))),
                }
            }
            Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l > r {
                            PreprocessingResult::Changed(Formula::ttrue())
                        } else {
                            PreprocessingResult::Changed(Formula::ffalse())
                        }
                    }
                    _ => PreprocessingResult::Unchanged(Formula::predicate(Predicate::Greater(
                        lhs.into(),
                        rhs.into(),
                    ))),
                }
            }
            Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l <= r {
                            PreprocessingResult::Changed(Formula::ttrue())
                        } else {
                            PreprocessingResult::Changed(Formula::ffalse())
                        }
                    }
                    _ => PreprocessingResult::Unchanged(Formula::predicate(Predicate::Leq(
                        lhs.into(),
                        rhs.into(),
                    ))),
                }
            }
            Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                match (lhs.is_const(), rhs.is_const()) {
                    (Some(l), Some(r)) => {
                        if l < r {
                            PreprocessingResult::Changed(Formula::ttrue())
                        } else {
                            PreprocessingResult::Changed(Formula::ffalse())
                        }
                    }
                    _ => PreprocessingResult::Unchanged(Formula::predicate(Predicate::Less(
                        lhs.into(),
                        rhs.into(),
                    ))),
                }
            }
            _ => PreprocessingResult::Unchanged(Formula::predicate(predicate)),
        }
    }
}

/// Infers integer substitutions from integer equalities with a single variable on one side.
pub struct IntSubstitutions {
    substitutions: Substitution,
}

impl Preprocessor for IntSubstitutions {
    fn get_substitution(&self) -> Option<Substitution> {
        Some(self.substitutions.clone())
    }

    fn get_name(&self) -> String {
        String::from("Integer substitutions")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {
            substitutions: Substitution::new(),
        }
    }

    fn apply_predicate(&mut self, predicate: Predicate, is_asserted: bool) -> PreprocessingResult {
        if is_asserted {
            match &predicate {
                Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                    if let IntTerm::Var(v) = lhs {
                        self.substitutions.set(&v, Term::Int(rhs.clone()));
                    } else if let IntTerm::Var(v) = rhs {
                        self.substitutions.set(&v, Term::Int(lhs.clone()));
                    }
                }
                _ => (),
            }
        }
        PreprocessingResult::Unchanged(Formula::predicate(predicate))
    }
}
