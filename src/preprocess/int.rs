//! Preprocessor for the `int` type.

use crate::{
    model::{
        formula::{Atom, Literal, NNFFormula, Predicate},
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

    fn apply_literal(&mut self, literal: Literal, _is_asserted: bool) -> PreprocessingResult {
        if let Atom::Predicate(p) = literal.atom() {
            match p {
                Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                    match (lhs.is_const(), rhs.is_const()) {
                        (Some(l), Some(r)) => {
                            if l == r {
                                if literal.is_pos() {
                                    PreprocessingResult::Changed(NNFFormula::ttrue())
                                } else {
                                    PreprocessingResult::Changed(NNFFormula::ffalse())
                                }
                            } else if literal.is_pos() {
                                PreprocessingResult::Changed(NNFFormula::ffalse())
                            } else {
                                PreprocessingResult::Changed(NNFFormula::ttrue())
                            }
                        }
                        _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
                    }
                }
                Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                    match (lhs.is_const(), rhs.is_const()) {
                        (Some(l), Some(r)) => {
                            if l >= r {
                                if literal.is_pos() {
                                    PreprocessingResult::Changed(NNFFormula::ttrue())
                                } else {
                                    PreprocessingResult::Changed(NNFFormula::ffalse())
                                }
                            } else if literal.is_pos() {
                                PreprocessingResult::Changed(NNFFormula::ffalse())
                            } else {
                                PreprocessingResult::Changed(NNFFormula::ttrue())
                            }
                        }
                        _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
                    }
                }
                Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                    match (lhs.is_const(), rhs.is_const()) {
                        (Some(l), Some(r)) => {
                            if l > r {
                                if literal.is_pos() {
                                    PreprocessingResult::Changed(NNFFormula::ttrue())
                                } else {
                                    PreprocessingResult::Changed(NNFFormula::ffalse())
                                }
                            } else if literal.is_pos() {
                                PreprocessingResult::Changed(NNFFormula::ffalse())
                            } else {
                                PreprocessingResult::Changed(NNFFormula::ttrue())
                            }
                        }
                        _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
                    }
                }
                Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                    match (lhs.is_const(), rhs.is_const()) {
                        (Some(l), Some(r)) => {
                            if l <= r {
                                if literal.is_pos() {
                                    PreprocessingResult::Changed(NNFFormula::ttrue())
                                } else {
                                    PreprocessingResult::Changed(NNFFormula::ffalse())
                                }
                            } else if literal.is_pos() {
                                PreprocessingResult::Changed(NNFFormula::ffalse())
                            } else {
                                PreprocessingResult::Changed(NNFFormula::ttrue())
                            }
                        }
                        _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
                    }
                }
                Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                    match (lhs.is_const(), rhs.is_const()) {
                        (Some(l), Some(r)) => {
                            if l < r {
                                if literal.is_pos() {
                                    PreprocessingResult::Changed(NNFFormula::ttrue())
                                } else {
                                    PreprocessingResult::Changed(NNFFormula::ffalse())
                                }
                            } else if literal.is_pos() {
                                PreprocessingResult::Changed(NNFFormula::ffalse())
                            } else {
                                PreprocessingResult::Changed(NNFFormula::ttrue())
                            }
                        }
                        _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
                    }
                }

                _ => PreprocessingResult::Unchanged(NNFFormula::Literal(literal)),
            }
        } else {
            PreprocessingResult::Unchanged(NNFFormula::Literal(literal))
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

    fn apply_literal(&mut self, literal: Literal, is_asserted: bool) -> PreprocessingResult {
        if is_asserted && literal.is_pos() {
            if let Atom::Predicate(Predicate::Equality(Term::Int(lhs), Term::Int(rhs))) =
                literal.atom()
            {
                if let IntTerm::Var(v) = lhs {
                    self.substitutions.set(v, Term::Int(rhs.clone()));
                } else if let IntTerm::Var(v) = rhs {
                    self.substitutions.set(v, Term::Int(lhs.clone()));
                }
            }
        }
        PreprocessingResult::Unchanged(NNFFormula::Literal(literal))
    }
}
