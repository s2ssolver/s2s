//! Representation of quantifier free first-order formulas and predicates

use std::fmt::Display;

use indexmap::IndexSet;

use crate::model::{regex::Regex, Variable};

use super::{
    integer::{IntTerm},
    words::{StringTerm},
    Evaluable, Sort, Substitutable, Substitution,
};

pub trait Sorted {
    fn sort(&self) -> Sort;
}

pub trait Alphabet {
    fn alphabet(&self) -> IndexSet<char>;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    String(StringTerm),
    Int(IntTerm),
    Regular(Regex),
    Bool(Box<Formula>),
}

impl Term {
    pub fn is_const(&self) -> bool {
        match self {
            Term::String(s) => s.is_const().is_some(),
            Term::Int(i) => i.is_const().is_some(),
            Term::Regular(_) => todo!(),
            Term::Bool(f) => f.is_const(),
        }
    }
}

impl From<StringTerm> for Term {
    fn from(s: StringTerm) -> Self {
        Term::String(s)
    }
}

impl From<IntTerm> for Term {
    fn from(i: IntTerm) -> Self {
        Term::Int(i)
    }
}

impl Sorted for Term {
    fn sort(&self) -> Sort {
        match self {
            Term::String(_) => Sort::String,
            Term::Int(_) => Sort::Int,
            Term::Regular(_) => Sort::String,
            Term::Bool(_) => Sort::Bool,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    Equality(Term, Term),
    Leq(Term, Term),
    Less(Term, Term),
    Geq(Term, Term),
    Greater(Term, Term),
    In(Term, Term),
}

pub enum Atom {
    Predicate(Predicate),
    BoolVar(Variable),
    True,
    False,
}

pub enum Literal {
    Pos(Atom),
    Neg(Atom),
}

// Todo: Implement TryFrom instead of panicing

/// A first-order formula with quantifiers.
/// A formula is inductive defined as follows:
/// - An [Atom] is a formula
/// - If `f` is a formula, then `¬f` ([Formula::Not]) is a formula
/// - If `f` and `g` are formulas, then `f ∧ g` ([Formula::And]) and `f ∨ g` ([Formula::Or]) are formulas
///
/// The variants [Formula::Not], [Formula::And], and [Formula::Or] should not be used directly but instead the corresponding constructors [Formula::not], [Formula::and], and [Formula::or], respectively, should be used.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Formula {
    True,
    False,
    BoolVar(Variable),
    Predicate(Predicate),
    /// A disjunction
    Or(Vec<Formula>),
    /// A conjunction
    And(Vec<Formula>),
    /// A negation
    Not(Box<Formula>),
}

impl Formula {
    /// Returns the formula `true`
    pub fn ttrue() -> Self {
        Self::True
    }

    /// Returns the formula `false`
    pub fn ffalse() -> Self {
        Self::False
    }

    /// Creates a new formula only consisting of a single Boolean variable
    pub fn bool(var: Variable) -> Self {
        Self::BoolVar(var)
    }

    /// Creates a new formula only consisting of a single predicate
    pub fn predicate(pred: Predicate) -> Self {
        Self::Predicate(pred)
    }

    /// Creates the conjunction of the given formulas.
    /// Performs some normalization:
    /// - If one of the formulas is `false`, returns `false`
    /// - If one of the formulas is `true`, removes it
    /// - If one of the formulas is a conjunction, adds its conjuncts (i.e. flattens the formula)
    pub fn and(fs: Vec<Formula>) -> Self {
        let mut conjs = Vec::new();
        for f in fs {
            match f {
                Formula::And(fs) => conjs.extend(fs),
                f => conjs.push(f),
            }
        }
        if conjs.is_empty() {
            Self::ttrue()
        } else if conjs.len() == 1 {
            conjs.into_iter().next().unwrap()
        } else {
            Self::And(conjs)
        }
    }

    /// Creates the disjunction of the given formulas.
    /// Performs some normalization:
    /// - If one of the formulas is `true`, returns `true`
    /// - If one of the formulas is `false`, removes it
    /// - If one of the formulas is a disjunction, adds its disjuncts (i.e. flattens the formula)
    pub fn or(fs: Vec<Formula>) -> Self {
        let mut disj = Vec::new();
        for f in fs {
            match f {
                Formula::Or(fs) => disj.extend(fs),
                f => disj.push(f),
            }
        }
        if disj.is_empty() {
            Self::ffalse()
        } else if disj.len() == 1 {
            disj.into_iter().next().unwrap()
        } else {
            Self::Or(disj)
        }
    }

    /// Creates the negation of the given formula.
    /// Flattens double negations.
    #[allow(clippy::should_implement_trait)]
    pub fn not(f: Formula) -> Self {
        match f {
            Formula::Not(f) => *f,
            f => Self::Not(Box::new(f)),
        }
    }

    /// Returns `true` if this formula is conjunctive, i.e., if it is a single atom or a conjunction of atoms.
    /// Returns `false` otherwise.
    pub fn is_conjunctive(&self) -> bool {
        match self {
            Formula::Or(_) => false,
            Formula::And(fs) => fs.iter().all(Self::is_conjunctive),
            Formula::Not(f) => f.is_conjunctive(),
            Formula::Predicate(_) | Formula::BoolVar(_) | Formula::True | Formula::False => true,
        }
    }

    /// Counts the number of atoms in this formula.
    pub fn num_atoms(&self) -> usize {
        match self {
            Formula::Predicate(_) | Formula::BoolVar(_) | Formula::True | Formula::False => 1,
            Formula::Or(fs) | Formula::And(fs) => fs.iter().map(Self::num_atoms).sum(),
            Formula::Not(f) => f.num_atoms(),
        }
    }

    /// Returns the atoms of this formula that need to be satisfied in every model.
    /// In other words, the conjunction of the returned atoms is entailed by this formula.
    ///
    /// TODO: This should return the asserted literals, not the asserted atoms. That is, it should return a list of atoms and their polarity in which they are asserted.
    pub fn asserted_atoms(&self) -> Vec<Atom> {
        match self {
            Formula::Predicate(a) => vec![Atom::Predicate(a.clone())],
            Formula::Or(_fs) => {
                vec![]
            }
            Formula::And(fs) => fs
                .iter()
                .map(Self::asserted_atoms)
                .fold(Vec::new(), |acc, x| acc.into_iter().chain(x).collect()),
            Formula::Not(_f) => vec![],
            Formula::True => vec![Atom::True],
            Formula::False => vec![Atom::True],
            Formula::BoolVar(v) => vec![Atom::BoolVar(v.clone())],
        }
    }

    /// Returns the alphabet of constants used in this formula.
    /// Collects the alphabet of all predicates occurring in this formula and returns the union of them.
    /// See [Predicate] for more information.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Formula::True => IndexSet::new(),
            Formula::False => IndexSet::new(),
            Formula::BoolVar(_) => IndexSet::new(),
            Formula::Predicate(p) => match p {
                Predicate::Equality(Term::String(lhs), Term::String(rhs))
                | Predicate::Leq(Term::String(lhs), Term::String(rhs))
                | Predicate::Less(Term::String(lhs), Term::String(rhs))
                | Predicate::Geq(Term::String(lhs), Term::String(rhs))
                | Predicate::Greater(Term::String(lhs), Term::String(rhs))
                | Predicate::In(Term::String(lhs), Term::String(rhs)) => {
                    let mut alphabet = lhs.alphabet();
                    alphabet.extend(rhs.alphabet());
                    alphabet
                }
                _ => IndexSet::new(),
            },
            Formula::Or(fs) | Formula::And(fs) => fs
                .iter()
                .map(Self::alphabet)
                .fold(IndexSet::new(), |acc, x| acc.union(&x).cloned().collect()),
            Formula::Not(f) => f.alphabet(),
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            Formula::True | Formula::False => true,
            Formula::BoolVar(_) => false,
            Formula::Predicate(p) => match p {
                Predicate::Equality(lhs, rhs)
                | Predicate::Leq(lhs, rhs)
                | Predicate::Less(lhs, rhs)
                | Predicate::Geq(lhs, rhs)
                | Predicate::Greater(lhs, rhs)
                | Predicate::In(lhs, rhs) => lhs.is_const() && rhs.is_const(),
            },
            Formula::Or(fs) | Formula::And(fs) => fs.iter().all(Self::is_const),
            Formula::Not(f) => f.is_const(),
        }
    }

    pub fn to_nnf(&self) -> Self {
        todo!("Implement NNF conversion")
    }
}

/* Substitution and Evaluation */

impl Substitutable for Formula {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        match self {
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::BoolVar(x) => match sub.get(x) {
                Some(Term::Bool(f)) => *f.clone(),
                // TODO: Return Result instead of panicing
                Some(_) => panic!(
                    "Cannot substitute Boolean variable {} with non-Boolean term",
                    x
                ),
                None => Formula::BoolVar(x.clone()),
            },
            Formula::Predicate(p) => Formula::Predicate(p.apply_substitution(sub)),
            Formula::Or(fs) => Formula::or(fs.iter().map(|f| f.apply_substitution(sub)).collect()),
            Formula::And(fs) => {
                Formula::and(fs.iter().map(|f| f.apply_substitution(sub)).collect())
            }
            Formula::Not(f) => Formula::not(f.apply_substitution(sub)),
        }
    }
}

impl Substitutable for Predicate {
    fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            Predicate::Equality(lhs, rhs) => {
                Predicate::Equality(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
            Predicate::Leq(lhs, rhs) => {
                Predicate::Leq(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
            Predicate::Less(lhs, rhs) => {
                Predicate::Less(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
            Predicate::Geq(lhs, rhs) => {
                Predicate::Geq(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
            Predicate::Greater(lhs, rhs) => {
                Predicate::Greater(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
            Predicate::In(lhs, rhs) => {
                Predicate::In(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
        }
    }
}

impl Substitutable for Term {
    fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            Term::String(s) => Term::String(s.apply_substitution(subs)),
            Term::Int(i) => Term::Int(i.apply_substitution(subs)),
            Term::Regular(_r) => todo!("Regular terms not implemented yet"),
            Term::Bool(f) => Term::Bool(Box::new(f.apply_substitution(subs))),
        }
    }
}

impl Evaluable for Formula {
    fn eval(&self, sub: &Substitution) -> Option<bool> {
        let res = match self {
            Formula::True => true,
            Formula::False => false,
            Formula::BoolVar(x) => match sub.get(x) {
                Some(Term::Bool(f)) => f.eval(sub)?,
                Some(_) => panic!(
                    "Cannot substitute Boolean variable {} with non-Boolean term",
                    x
                ),
                None => return None,
            },
            Formula::Predicate(p) => p.eval(sub)?,
            Formula::Or(fs) => {
                let mut iter = fs.iter().map(|f| f.eval(sub));
                if iter.any(|t| t == Some(true)) {
                    true
                } else if iter.all(|f| f == Some(false)) {
                    false
                } else {
                    return None;
                }
            }
            Formula::And(fs) => {
                let mut iter = fs.iter().map(|f| f.eval(sub));
                if iter.all(|t| t == Some(true)) {
                    true
                } else if iter.any(|f| f == Some(false)) {
                    false
                } else {
                    return None;
                }
            }
            Formula::Not(f) => !f.eval(sub)?,
        };
        Some(res)
    }
}

impl Evaluable for Predicate {
    fn eval(&self, sub: &Substitution) -> Option<bool> {
        let res = match self {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l == r,
                    (_, _) => return None,
                }
            }
            Predicate::Equality(Term::Int(lhs), Term::Int(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l == r,
                    (_, _) => return None,
                }
            }
            Predicate::Equality(l, r) => {
                panic!("= unsupported to sorts {} and {}", l.sort(), r.sort())
            }
            Predicate::Leq(Term::Int(lhs), Term::Int(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l <= r,
                    (_, _) => return None,
                }
            }
            Predicate::Leq(l, r) => panic!("<= unsupported to sorts {} and {}", l.sort(), r.sort()),
            Predicate::Less(Term::Int(lhs), Term::Int(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l <= r,
                    (_, _) => return None,
                }
            }
            Predicate::Less(l, r) => {
                panic!("< unsupported for sorts {} and {}", l.sort(), r.sort())
            }
            Predicate::Geq(Term::Int(lhs), Term::Int(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l <= r,
                    (_, _) => return None,
                }
            }
            Predicate::Geq(l, r) => {
                panic!(">= unsupported for sorts {} and {}", l.sort(), r.sort())
            }
            Predicate::Greater(Term::Int(lhs), Term::Int(rhs)) => {
                match (
                    lhs.apply_substitution(sub).is_const(),
                    rhs.apply_substitution(sub).is_const(),
                ) {
                    (Some(l), Some(r)) => l <= r,
                    (_, _) => return None,
                }
            }
            Predicate::Greater(l, r) => {
                panic!("> unsupported for sorts {} and {}", l.sort(), r.sort())
            }
            Predicate::In(_, _) => todo!(),
        };
        Some(res)
    }
}

/* Pretty Printing */

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Predicate(p) => write!(f, "{}", p),
            Atom::BoolVar(v) => write!(f, "{}", v),
            Atom::True => write!(f, "true"),
            Atom::False => write!(f, "false"),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::String(t) => write!(f, "{}", t),
            Term::Int(t) => write!(f, "{}", t),
            Term::Bool(t) => write!(f, "{}", t),
            Term::Regular(_r) => todo!(),
        }
    }
}

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Equality(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
            Predicate::Leq(lhs, rhs) => write!(f, "{} <= {}", lhs, rhs),
            Predicate::Less(lhs, rhs) => write!(f, "{} < {}", lhs, rhs),
            Predicate::Geq(lhs, rhs) => write!(f, "{} >= {}", lhs, rhs),
            Predicate::Greater(lhs, rhs) => write!(f, "{} > {}", lhs, rhs),
            Predicate::In(lhs, rhs) => write!(f, "{} in {}", lhs, rhs),
        }
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::BoolVar(v) => write!(f, "{}", v),
            Formula::Predicate(p) => write!(f, "{}", p),
            Formula::Or(fs) => {
                write!(f, "(")?;
                let mut first = true;
                for fm in fs {
                    if !first {
                        write!(f, r" \/ ")?;
                    }
                    write!(f, "{}", fm)?;
                    first = false;
                }
                write!(f, ")")
            }
            Formula::And(fs) => {
                write!(f, "(")?;
                let mut first = true;
                for fm in fs {
                    if !first {
                        write!(f, r" /\ ")?;
                    }
                    write!(f, "{}", fm)?;
                    first = false;
                }
                write!(f, ")")
            }
            Formula::Not(fm) => write!(f, "¬{}", fm),
        }
    }
}

#[cfg(test)]
mod test {

    #[test]
    #[ignore = "Test not implemented yet"]
    fn formula_and_normalize() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn formula_or_normalize() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn formula_not_normalize() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn formula_conjunctive() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn asserted_atoms_conjunctive() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn asserted_atoms_disjunction() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented yet"]
    fn asserted_atoms_mixed() {
        todo!()
    }
}
