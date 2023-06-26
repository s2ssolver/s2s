//! Algebraic representation of the predicates in the input formula.

mod integer;
mod string;

pub use integer::*;
pub use string::*;

use crate::error::Error;

use super::{
    formula::{Formula, Predicate},
    terms::{StringTerm, Term},
};

/// A constraint is a combinatorial problem over a set of variables.
/// To solve an input formula, a combination of constraints that satisfy the formula is solved.
/// Thus, constraints are subject of the encoding process.
/// It can be a [WordEquation], a [LinearConstraint], or a [RegularConstraint].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
    WordEquation(WordEquation),
    LinearConstraint(LinearConstraint),
    RegularConstraint(RegularConstraint),
}

/* Conversions between constraints and predicates */

impl TryFrom<Predicate> for Constraint {
    type Error = Error;

    fn try_from(value: Predicate) -> Result<Self, Self::Error> {
        match value {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => Ok(
                Constraint::WordEquation(WordEquation::new(lhs.into(), rhs.into())),
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
                let con = RegularConstraint::new(re.try_into()?, pat.into());
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
            StringTerm::Constant(word) => Self::constant(&word.iter().collect::<String>()),
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
                Ok(Self::new(lhs.into(), rhs.into()))
            }
            _ => Err(()),
        }
    }
}

impl From<WordEquation> for Predicate {
    fn from(val: WordEquation) -> Self {
        Predicate::Equality(
            Term::String(val.lhs().clone().into()),
            Term::String(val.rhs().clone().into()),
        )
    }
}

impl From<WordEquation> for Formula {
    fn from(val: WordEquation) -> Self {
        let lhs = Term::String(val.lhs().clone().into());
        let rhs = Term::String(val.rhs().clone().into());
        Formula::predicate(Predicate::Equality(lhs, rhs))
    }
}

impl From<(StringTerm, StringTerm)> for WordEquation {
    fn from(value: (StringTerm, StringTerm)) -> Self {
        Self::new(value.0.into(), value.1.into())
    }
}
