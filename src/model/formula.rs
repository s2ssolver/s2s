//! Representation of quantifier free first-order formulas and predicates

use std::fmt::Display;

use indexmap::IndexSet;

use crate::model::{
    integer::LinearConstraint,
    regex::Regex,
    words::{Pattern, WordEquation},
    Variable,
};

use super::{Proposition, Substitutable, VarSubstitutions};

/// A predicate, which is either a word equation, a regular constraint, or a linear constraint.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    /// A word equation
    WordEquation(WordEquation),
    /// A regular constraint
    RegularConstraint(Pattern, Regex),
    /// A linear constraint
    LinearConstraint(LinearConstraint),
}

impl Predicate {
    /// Create a new predicate from a given word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::WordEquation(eq)
    }

    /// Create a new predicate from a given regular constraint
    pub fn regular_constraint(p: Pattern, r: Regex) -> Self {
        Self::RegularConstraint(p, r)
    }

    /// Returns the alphabet of constants used in this predicate.
    /// For word equations and regular constraints, this is the union of the constant occurring.
    /// For linear constraints, the alphabet is empty.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Predicate::WordEquation(eq) => eq.alphabet(),
            Predicate::LinearConstraint(_) => IndexSet::new(),
            Predicate::RegularConstraint(_, _) => todo!("Regular Constraints not supported yet"),
        }
    }
}

/// An atomic formula.
/// An atomic formula is either a predicate, a boolean variable, or the constant true or false.
#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
    /// A predicate
    Predicate(Predicate),
    /// A boolean variable
    BoolVar(Variable),
    /// The constant true
    True,
    /// The constant false
    False,
}

impl Atom {
    /// Create a new atom from a word equation
    pub fn word_equation(eq: WordEquation) -> Self {
        Self::Predicate(Predicate::WordEquation(eq))
    }
}

/// A first-order formula with quantifiers.
/// A formula is inductive defined as follows:
/// - An [Atom] is a formula
/// - If `f` is a formula, then `¬f` ([Formula::Not]) is a formula
/// - If `f` and `g` are formulas, then `f ∧ g` ([Formula::And]) and `f ∨ g` ([Formula::Or]) are formulas
///
/// The variants [Formula::Not], [Formula::And], and [Formula::Or] should not be used directly but instead the corresponding constructors [Formula::not], [Formula::and], and [Formula::or], respectively, should be used.
#[derive(Clone, Debug, PartialEq)]
pub enum Formula {
    /// An atom
    Atom(Atom),
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
        Self::Atom(Atom::True)
    }

    /// Returns the formula `false`
    pub fn ffalse() -> Self {
        Self::Atom(Atom::True)
    }

    /// Creates a new formula only consisting of a single Boolean variable
    pub fn bool(var: Variable) -> Self {
        Self::Atom(Atom::BoolVar(var))
    }

    /// Creates a new formula only consisting of a single predicate
    pub fn predicate(pred: Predicate) -> Self {
        Self::Atom(Atom::Predicate(pred))
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
            Formula::Atom(_) => true,
            Formula::Or(_) => false,
            Formula::And(fs) => fs.iter().all(Self::is_conjunctive),
            Formula::Not(f) => f.is_conjunctive(),
        }
    }

    /// Counts the number of atoms in this formula.
    pub fn num_atoms(&self) -> usize {
        match self {
            Formula::Atom(_) => 1,
            Formula::Or(fs) | Formula::And(fs) => fs.iter().map(Self::num_atoms).sum(),
            Formula::Not(f) => f.num_atoms(),
        }
    }

    /// Returns the atoms of this formula that need to be satisfied in every model.
    /// In other words, the conjunction of the returned atoms is entailed by this formula.
    ///
    /// TODO: This should return the asserted literals, not the asserted atoms. That is, it should return a list of atoms and their polarity in which they are asserted.
    pub fn asserted_atoms(&self) -> Vec<&Atom> {
        match self {
            Formula::Atom(a) => vec![a],
            Formula::Or(_fs) => {
                vec![]
            }
            Formula::And(fs) => fs
                .iter()
                .map(Self::asserted_atoms)
                .fold(Vec::new(), |acc, x| acc.into_iter().chain(x).collect()),
            Formula::Not(_f) => vec![],
        }
    }

    /// Returns the alphabet of constants used in this formula.
    /// Collects the alphabet of all predicates occurring in this formula and returns the union of them.
    /// See [Predicate] for more information.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            Formula::Atom(a) => match a {
                Atom::Predicate(p) => p.alphabet(),
                Atom::BoolVar(_) => IndexSet::new(),
                Atom::True => IndexSet::new(),
                Atom::False => IndexSet::new(),
            },
            Formula::Or(fs) | Formula::And(fs) => fs
                .iter()
                .map(Self::alphabet)
                .fold(IndexSet::new(), |acc, x| acc.union(&x).cloned().collect()),
            Formula::Not(f) => f.alphabet(),
        }
    }

    /// Returns `Some(true)` if the given substitution is a solution to this formula.
    /// Returns `Some(false)` if the given substitution is not a solution to this formula.
    /// Returns `None` if it is not possible to determine whether the given substitution is a solution to this formula.
    pub fn is_solution(&self, subs: &VarSubstitutions) -> Option<bool> {
        self.substitute(subs).truth_value()
    }
}

/* Substitutions */

impl Substitutable for Predicate {
    fn substitute(&self, subst: &VarSubstitutions) -> Self {
        match self {
            Predicate::WordEquation(eq) => Predicate::WordEquation(eq.substitute(subst)),
            Predicate::RegularConstraint(_, _) => {
                todo!("Regular Constraints not supported yet")
            }
            Predicate::LinearConstraint(l) => Predicate::LinearConstraint(l.substitute(subst)),
        }
    }
}

impl Substitutable for Atom {
    fn substitute(&self, subst: &VarSubstitutions) -> Self {
        match self {
            Atom::Predicate(p) => Atom::Predicate(p.substitute(subst)),
            Atom::BoolVar(x) => match subst.get_bool(x) {
                Some(true) => Atom::True,
                Some(false) => Atom::False,
                None => Atom::BoolVar(x.clone()),
            },
            _ => self.clone(),
        }
    }
}

impl Substitutable for Formula {
    fn substitute(&self, subst: &VarSubstitutions) -> Self {
        match self {
            Formula::Atom(a) => Formula::Atom(a.substitute(subst)),
            Formula::Or(fs) => Formula::Or(fs.iter().map(|f| f.substitute(subst)).collect()),
            Formula::And(fs) => Formula::And(fs.iter().map(|f| f.substitute(subst)).collect()),
            Formula::Not(f) => Formula::Not(Box::new(f.substitute(subst))),
        }
    }
}

impl Proposition for Predicate {
    fn truth_value(&self) -> Option<bool> {
        match self {
            Predicate::WordEquation(eq) => eq.truth_value(),
            Predicate::RegularConstraint(_, _) => todo!("Regular Constraints not supported yet"),
            Predicate::LinearConstraint(l) => l.truth_value(),
        }
    }
}

impl Proposition for Atom {
    fn truth_value(&self) -> Option<bool> {
        match self {
            Atom::Predicate(p) => p.truth_value(),
            Atom::BoolVar(_) => None,
            Atom::True => Some(true),
            Atom::False => Some(false),
        }
    }
}

impl Proposition for Formula {
    fn truth_value(&self) -> Option<bool> {
        match self {
            Formula::Atom(a) => a.truth_value(),
            Formula::Or(fs) => fs
                .iter()
                .fold(Some(false), |acc, f| match (acc, f.truth_value()) {
                    (Some(true), _) => Some(true),
                    (_, Some(true)) => Some(true),
                    (Some(false), None) => None,
                    (None, Some(false)) => None,
                    (None, None) => None,
                    (Some(false), Some(false)) => Some(false),
                }),
            Formula::And(fs) => fs
                .iter()
                .fold(Some(true), |acc, f| match (acc, f.truth_value()) {
                    (Some(false), _) => Some(false),
                    (_, Some(false)) => Some(false),
                    (Some(true), None) => None,
                    (None, Some(true)) => None,
                    (None, None) => None,
                    (Some(true), Some(true)) => Some(true),
                }),
            Formula::Not(f) => match f.truth_value() {
                Some(true) => Some(false),
                Some(false) => Some(true),
                None => None,
            },
        }
    }
}

/* Pretty Printing */

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::WordEquation(weq) => write!(f, "{}", weq),
            Predicate::RegularConstraint(_, _) => todo!(),
            Predicate::LinearConstraint(c) => write!(f, "{}", c),
        }
    }
}

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

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::Atom(a) => write!(f, "{}", a),
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
