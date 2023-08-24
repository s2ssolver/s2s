//! Algebraic representation of the predicates in the input formula.

mod integer;
mod string;

use std::fmt::Display;

use indexmap::{indexset, IndexSet};
pub use integer::*;
pub use string::*;

use crate::error::Error;

use super::{
    formula::{Atom, Formula, Literal, Predicate},
    terms::{StringTerm, Term},
    Variable,
};

/// A constraint is a combinatorial problem over a set of variables.
/// To solve an input formula, a combination of constraints that satisfy the formula is solved.
/// Thus, constraints are subject of the encoding process.
/// It can be a [WordEquation], a [LinearConstraint], or a [RegularConstraint].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
    /// A word equation is a constraint of the form `a = b`, where `a` and `b` are [Pattern].
    /// If the second argument is `true`, the equation is interpreted as a disequation, i.e., `a != b`.
    WordEquation(WordEquation),
    /// A linear arithmetic constraint is a constraint of the form `a # b`, where `a` and `b` are [LinearArithTerm] and `#` is a variant of [LinearConstraintType] .
    LinearConstraint(LinearConstraint),
    /// A regular constraint is a constraint of the form `a in b`, where `a` is a [Pattern] and `b` is a [RegularConstraint].
    /// If the second argument is `true`, the constraint is interpreted as `a not in b`.
    RegularConstraint(RegularConstraint),
    /// A boolean variable constraint is a constraint of the form `a` or `not a`, where `a` is a [Variable] of sort Boolean.
    BoolVarConstraint(Variable, bool),
}

impl Constraint {
    pub fn vars(&self) -> IndexSet<Variable> {
        match self {
            Constraint::WordEquation(eq) => eq.variables(),
            Constraint::LinearConstraint(l) => l.lhs().vars(),
            Constraint::RegularConstraint(r) => r.get_pattern().vars(),
            Constraint::BoolVarConstraint(v, _) => indexset![v.clone()],
        }
    }
}

/* Conversions between constraints and predicates */

impl TryFrom<Literal> for Constraint {
    type Error = Error;

    fn try_from(value: Literal) -> Result<Self, Self::Error> {
        match value {
            Literal::Pos(Atom::BoolVar(v)) => Ok(Constraint::BoolVarConstraint(v, true)),
            Literal::Neg(Atom::BoolVar(v)) => Ok(Constraint::BoolVarConstraint(v, false)),
            Literal::Pos(Atom::Predicate(predicate)) => Constraint::try_from(predicate),
            Literal::Neg(Atom::Predicate(predicate)) => match Constraint::try_from(predicate)? {
                Constraint::WordEquation(mut eq) => {
                    eq.set_inequality();
                    Ok(Constraint::WordEquation(eq))
                }
                Constraint::LinearConstraint(mut l) => match l.typ {
                    LinearConstraintType::Eq => {
                        l.typ = LinearConstraintType::Ineq;
                        Ok(Constraint::LinearConstraint(l))
                    }
                    LinearConstraintType::Ineq => {
                        l.typ = LinearConstraintType::Eq;
                        Ok(Constraint::LinearConstraint(l))
                    }
                    LinearConstraintType::Leq => {
                        l.typ = LinearConstraintType::Greater;
                        Ok(Constraint::LinearConstraint(l))
                    }
                    LinearConstraintType::Less => {
                        l.typ = LinearConstraintType::Geq;
                        Ok(Constraint::LinearConstraint(l))
                    }
                    LinearConstraintType::Geq => {
                        l.typ = LinearConstraintType::Less;
                        Ok(Constraint::LinearConstraint(l))
                    }
                    LinearConstraintType::Greater => {
                        l.typ = LinearConstraintType::Leq;
                        Ok(Constraint::LinearConstraint(l))
                    }
                },
                Constraint::RegularConstraint(mut r) => {
                    r.set_type_notin();
                    Ok(Constraint::RegularConstraint(r))
                }
                Constraint::BoolVarConstraint(a, _) => Ok(Constraint::BoolVarConstraint(a, false)),
            },
            _ => Err(Error::SolverError(format!("Not a constrait {}", value))),
        }
    }
}

impl TryFrom<Predicate> for Constraint {
    type Error = Error;

    fn try_from(value: Predicate) -> Result<Self, Self::Error> {
        match value {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => Ok(
                Constraint::WordEquation(WordEquation::new_equality(lhs.into(), rhs.into())),
            ),
            Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Eq));
                Ok(Constraint::LinearConstraint(con))
            }
            Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);

                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Leq));
                Ok(Constraint::LinearConstraint(con))
            }
            Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Less));
                Ok(Constraint::LinearConstraint(con))
            }
            Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Geq));
                Ok(Constraint::LinearConstraint(con))
            }
            Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                let lin_lhs = LinearArithTerm::from(lhs);
                let lin_rhs = LinearArithTerm::from(rhs);
                let con = LinearConstraint::from((lin_lhs, lin_rhs, LinearConstraintType::Greater));
                Ok(Constraint::LinearConstraint(con))
            }
            Predicate::In(Term::String(pat), Term::Regular(re)) => {
                let con = RegularConstraint::new_in(re.try_into()?, pat.into());
                Ok(Constraint::RegularConstraint(con))
            }
            // Unsupported
            Predicate::Leq(Term::String(_), Term::String(_))
            | Predicate::Less(Term::String(_), Term::String(_))
            | Predicate::Geq(Term::String(_), Term::String(_))
            | Predicate::Greater(Term::String(_), Term::String(_)) => {
                Err(Error::unsupported("Lexicographic order"))
            }
            // Undefined
            _ => Err(Error::SolverError(format!("Undefined predicate {}", value))),
        }
    }
}

impl From<StringTerm> for Pattern {
    fn from(value: StringTerm) -> Self {
        match value {
            StringTerm::Variable(var) => Self::variable(&var),
            StringTerm::Constant(word) => {
                Self::new(word.iter().map(|c| Symbol::Constant(*c)).collect())
            }
            StringTerm::Concat(lhs, rhs) => {
                let mut res = Self::from(*lhs);
                res.extend(Self::from(*rhs));
                res
            }
        }
    }
}

impl From<Pattern> for StringTerm {
    fn from(value: Pattern) -> Self {
        let mut res = StringTerm::empty();
        for symbol in value.symbols() {
            match symbol {
                Symbol::Constant(c) => res = StringTerm::concat_const(res, &c.to_string()),
                Symbol::Variable(v) => res = StringTerm::concat_var(res, v),
            }
        }
        res
    }
}

impl TryFrom<Predicate> for WordEquation {
    type Error = (); // Todo: better error type

    fn try_from(value: Predicate) -> Result<Self, Self::Error> {
        match value {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                Ok(Self::new_equality(lhs.into(), rhs.into()))
            }
            _ => Err(()),
        }
    }
}

impl From<WordEquation> for Predicate {
    fn from(val: WordEquation) -> Self {
        Predicate::Equality(
            Term::String(val.lhs().into()),
            Term::String(val.rhs().into()),
        )
    }
}

impl From<WordEquation> for Formula {
    fn from(val: WordEquation) -> Self {
        let lhs = Term::String(val.lhs().into());
        let rhs = Term::String(val.rhs().into());
        Formula::predicate(Predicate::Equality(lhs, rhs))
    }
}

impl From<(StringTerm, StringTerm)> for WordEquation {
    fn from(value: (StringTerm, StringTerm)) -> Self {
        Self::new_equality(value.0.into(), value.1.into())
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::WordEquation(eq) => write!(f, "{}", eq),
            Constraint::LinearConstraint(l) => write!(f, "{}", l),
            Constraint::RegularConstraint(re) => {
                if re.get_type().is_in() {
                    write!(f, "{} in {}", re.get_pattern(), re.get_re())
                } else {
                    write!(f, "{} notin {}", re.get_pattern(), re.get_re())
                }
            }
            Constraint::BoolVarConstraint(c, p) => {
                if *p {
                    write!(f, "{}", c)
                } else {
                    write!(f, "not {}", c)
                }
            }
        }
    }
}
