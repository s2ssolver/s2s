//! Representation of quantifier free first-order formulas and predicates

use std::{fmt::Display, vec};

use indexmap::{indexset, IndexSet};
use quickcheck::Arbitrary;
use regulaer::{re::Regex, RegLang};

use crate::model::Variable;

use super::{terms::Term, Evaluable, Sort, Substitutable, Substitution};

pub trait Sorted {
    fn sort(&self) -> Sort;
}

pub trait Alphabet {
    fn alphabet(&self) -> IndexSet<char>;
}

/// Predicates are, besides purely boolean variable, the atomic formulas of first-order logic.
/// Predicates are relations over [Terms] that are either true or false.
/// The following predicates are supported:
/// - Equality (`=`) between two terms
/// - Inequalities (`<=`, `<`, `>=`, `>`) between two terms
/// - Membership (`in`) of a term in a language defined by a term
///
/// Note that the predicates are overloaded, i.e., their semantics depends on the sorts of the terms.
/// For example, the predicates `<=`, `<`, `>=`, `>` compare terms of sort `Int` arithmetically and terms of sort `String` lexicographically.
/// Moreover, not all predicates are supported for all sorts.
/// For example, the predicate `in` is only defined for terms of sort `String` and `ReLang`.
/// Lastly note that not all semantically sound predicates are supported by the solver.
/// For instance, lexicographic ordering of strings is not supported.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    Equality(Term, Term),
    Leq(Term, Term),
    Less(Term, Term),
    Geq(Term, Term),
    Greater(Term, Term),
    In(Term, Term),
}

impl Predicate {
    /// Returns the signature of the arguments of this predicate.
    pub fn signature(&self) -> Vec<Sort> {
        match self {
            Predicate::Equality(lhs, rhs)
            | Predicate::Leq(lhs, rhs)
            | Predicate::Less(lhs, rhs)
            | Predicate::Geq(lhs, rhs)
            | Predicate::Greater(lhs, rhs)
            | Predicate::In(lhs, rhs) => vec![lhs.sort(), rhs.sort()],
        }
    }

    pub fn equality(lhs: &Term, rhs: &Term) -> Self {
        Self::Equality(lhs.clone(), rhs.clone())
    }

    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            Predicate::Equality(lhs, rhs)
            | Predicate::Leq(lhs, rhs)
            | Predicate::Less(lhs, rhs)
            | Predicate::Geq(lhs, rhs)
            | Predicate::Greater(lhs, rhs)
            | Predicate::In(lhs, rhs) => {
                let mut vars = lhs.vars();
                vars.extend(rhs.vars());
                vars
            }
        }
    }
}

/// The atomic formulas of first-order logic, which are either [Predicate]s, Boolean [Variable]s, or the constants `True` and `False`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Atom {
    Predicate(Predicate),
    BoolVar(Variable),
    True,
    False,
}

impl Atom {
    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            Atom::Predicate(p) => p.vars(),
            Atom::BoolVar(x) => indexset! {x},
            Atom::True => indexset! {},
            Atom::False => indexset! {},
        }
    }
}

/// A literal is an atom or the negation of an atom.
/// The purpose of the enum is to enumerate the literals of a formula, it is not used to represent formulas.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Pos(Atom),
    Neg(Atom),
}

impl Literal {
    /// Returns `true` iff this literal is a positive atom.
    pub fn is_pos(&self) -> bool {
        match self {
            Literal::Pos(_) => true,
            Literal::Neg(_) => false,
        }
    }

    /// Returns `true` iff this literal is a negative atom.
    pub fn is_neg(&self) -> bool {
        !self.is_pos()
    }

    /// Returns the atom of this literal.
    pub fn atom(&self) -> &Atom {
        match self {
            Literal::Pos(a) | Literal::Neg(a) => a,
        }
    }

    /// Returns `true` iff this literal is a predicate and `false` otherwise.
    pub fn is_predicate(&self) -> bool {
        matches!(
            self,
            Literal::Pos(Atom::Predicate(_)) | Literal::Neg(Atom::Predicate(_))
        )
    }
}

/// A first-order formula without quantifiers.
/// A formula is inductive defined as follows:
/// - An [Atom] is a formula
/// - If `f` is a formula, then `¬f` ([Formula::Not]) is a formula
/// - If `f` and `g` are formulas, then `f ∧ g` ([Formula::And]) and `f ∨ g` ([Formula::Or]) are formulas
///
/// The variants should not be used directly but instead the corresponding constructors should be used.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Formula {
    Atom(Atom),
    /// A disjunction
    Or(Vec<Formula>),
    /// A conjunction
    And(Vec<Formula>),
    /// A negation
    Not(Box<Formula>),
}

impl Formula {
    /// Returns the formula `true`.
    /// This is a shortcut for `Formula::Atom(Atom::True)`.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Atom};
    /// assert_eq!(Formula::ttrue(), Formula::Atom(Atom::True));
    /// ```
    pub fn ttrue() -> Self {
        Self::Atom(Atom::True)
    }

    /// Returns the formula `false`.
    /// This is a shortcut for `Formula::Atom(Atom::False)`.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Atom};
    /// assert_eq!(Formula::ffalse(), Formula::Atom(Atom::False));
    /// ```
    pub fn ffalse() -> Self {
        Self::Atom(Atom::False)
    }

    /// Creates a new formula only consisting of a single Boolean variable
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate, Atom};
    /// use satstr::model::terms::Term;
    /// use satstr::model::{Variable, Sort};
    /// let x = Variable::new(String::from("x"), Sort::Bool);
    /// assert_eq!(Formula::boolvar(x.clone()), Formula::Atom(Atom::BoolVar(x)));
    /// ```
    pub fn boolvar(var: Variable) -> Self {
        Self::Atom(Atom::BoolVar(var))
    }

    /// Creates a new formula only consisting of a single [Predicate].
    /// This is a shortcut for `Formula::Atom(Atom::Predicate(pred))`.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate, Atom};
    /// use satstr::model::terms::Term;
    /// let pred = Predicate::Equality(Term::Int(1.into()), Term::Int(2.into()));
    /// assert_eq!(Formula::predicate(pred.clone()), Formula::Atom(Atom::Predicate(pred)));
    /// ```
    pub fn predicate(pred: Predicate) -> Self {
        Self::Atom(Atom::Predicate(pred))
    }

    /// Creates the conjunction of the given formulas.
    /// Performs some normalization:
    /// - If one of the formulas is `false`, returns `false`
    /// - If one of the formulas is `true`, removes it
    /// - If one of the formulas is a conjunction, adds its conjuncts (i.e. flattens the formula)
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// assert_eq!(Formula::and(vec![f1.clone(), f2.clone(), f3.clone()]), f1);
    /// assert_eq!(Formula::and(vec![f2.clone(), f3.clone()]), f3);
    /// ```
    pub fn and(fs: Vec<Formula>) -> Self {
        let mut conjs = Vec::new();
        for f in fs {
            match f {
                Formula::And(fs) => conjs.extend(fs),
                Formula::Atom(Atom::False) => return Self::ffalse(),
                Formula::Atom(Atom::True) => (),
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
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// assert_eq!(Formula::or(vec![f1.clone(), f2.clone(), f3.clone()]), f2);
    /// assert_eq!(Formula::or(vec![f1.clone(), f3.clone()]), f3);
    /// ```
    pub fn or(fs: Vec<Formula>) -> Self {
        let mut disj = Vec::new();
        for f in fs {
            match f {
                Formula::Or(fs) => disj.extend(fs),
                Formula::Atom(Atom::True) => return Self::ttrue(),
                Formula::Atom(Atom::False) => (),
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
    /// Flattens double negations and replaces negations of `true` and `false` with the corresponding constants.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// assert_eq!(Formula::not(f1.clone()), f2);
    /// assert_eq!(Formula::not(f2.clone()), f1);
    /// assert_eq!(Formula::not(f3.clone()), Formula::Not(Box::new(f3.clone())));
    /// assert_eq!(Formula::not(Formula::not(f3.clone())), f3.clone());
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn not(f: Formula) -> Self {
        match f {
            Formula::Atom(Atom::True) => Self::ffalse(),
            Formula::Atom(Atom::False) => Self::ttrue(),
            Formula::Not(f) => *f,
            f => Self::Not(Box::new(f)),
        }
    }

    /// Returns the variables occurring in this formula.
    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            Formula::Atom(a) => a.vars(),
            Formula::Or(fs) | Formula::And(fs) => fs.iter().fold(indexset!(), |mut s, f| {
                s.extend(f.vars());
                s.into_iter().collect()
            }),
            Formula::Not(f) => f.vars(),
        }
    }

    /// Returns `true` if this formula is conjunctive, i.e., if it is a single atom or a conjunction of atoms.
    /// Returns `false` otherwise.
    /// Note that this function does not check if the formula is in conjunctive normal form.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// assert!(f1.is_conjunctive());
    /// assert!(Formula::And(vec![f1.clone(), f2.clone(), f3.clone()]).is_conjunctive());
    /// assert!(!Formula::Or(vec![f1.clone(), f2.clone(), f3.clone()]).is_conjunctive());
    /// ```
    pub fn is_conjunctive(&self) -> bool {
        match self {
            Formula::Or(_) => false,
            Formula::And(fs) => fs.iter().all(Self::is_conjunctive),
            Formula::Not(f) => f.is_conjunctive(),
            Formula::Atom(_) => true,
        }
    }

    /// Counts the number of atoms in this formula.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// assert_eq!(f1.num_atoms(), 1);
    /// assert_eq!(Formula::And(vec![f1.clone(), f3.clone()]).num_atoms(), 2);
    /// assert_eq!(Formula::Or(vec![f1.clone(), Formula::And(vec![f2.clone(), f3.clone()])]).num_atoms(), 3);
    /// assert_eq!(Formula::Not(Box::new(f3.clone())).num_atoms(), 1);
    /// ```
    pub fn num_atoms(&self) -> usize {
        match self {
            Formula::Atom(_) => 1,
            Formula::Or(fs) | Formula::And(fs) => fs.iter().map(Self::num_atoms).sum(),
            Formula::Not(f) => f.num_atoms(),
        }
    }

    /// Returns the atoms of this formula that need to be satisfied in every model.
    /// In other words, the conjunction of the returned atoms is entailed by this formula.
    /// This is the case for all atoms in a conjunction, but not for atoms in a disjunction.
    /// An atom that is negated is also not entailed by the formula, see [Formula::asserted_literals].
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate, Atom};
    /// use satstr::model::terms::Term;
    ///
    /// let f1 = Formula::ffalse();
    /// let f2 = Formula::ttrue();
    /// let a = Predicate::Equality(Term::Int(1.into()), Term::Int(2.into()));
    /// let f3 = Formula::predicate(a.clone());
    /// assert_eq!(f1.asserted_atoms(), vec![Atom::False]);
    /// assert_eq!(Formula::And(vec![f1.clone(), f2.clone(), f3.clone()]).asserted_atoms(), vec![Atom::False, Atom::True, Atom::Predicate(a)]);
    /// assert_eq!(Formula::Or(vec![f1.clone(), f2.clone(), f3.clone()]).asserted_atoms(), vec![]);
    /// assert_eq!(Formula::And(vec![f1.clone(), Formula::Or(vec![f2.clone(), f3.clone()])]).asserted_atoms(), vec![Atom::False]);
    /// assert_eq!(Formula::not(f3.clone()).asserted_atoms(), vec![]);
    /// ```
    pub fn asserted_atoms(&self) -> Vec<Atom> {
        match self {
            Formula::Atom(a) => vec![a.clone()],
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

    /// Returns true if the formula contains no variables.
    /// This is the case if all literals occirring in the formula do not contain variables.
    ///
    /// # Example
    /// ```rust
    /// use satstr::model::formula::{Formula, Predicate, Atom};
    /// use satstr::model::terms::{Term, IntTerm};
    /// use satstr::model::{Variable, Sort};
    ///
    /// let f1 = Formula::boolvar(Variable::temp(Sort::Bool));
    /// let f2 = Formula::predicate(Predicate::Equality(Term::Int(1.into()), Term::Int(2.into())));
    /// let f3 = Formula::predicate(Predicate::Equality(Term::Int(IntTerm::Var(Variable::temp(Sort::Int))), Term::Int(2.into())));
    /// assert!(!f1.is_ground());
    /// assert!(f2.is_ground());
    /// assert!(!f3.is_ground());
    /// assert!(!Formula::and(vec![f1.clone(), f2.clone(), f3.clone()]).is_ground());
    /// ```
    pub fn is_ground(&self) -> bool {
        match self {
            Formula::Atom(Atom::True) | Formula::Atom(Atom::False) => true,
            Formula::Atom(Atom::BoolVar(_)) => false,
            Formula::Atom(Atom::Predicate(p)) => match p {
                Predicate::Equality(lhs, rhs)
                | Predicate::Leq(lhs, rhs)
                | Predicate::Less(lhs, rhs)
                | Predicate::Geq(lhs, rhs)
                | Predicate::Greater(lhs, rhs)
                | Predicate::In(lhs, rhs) => lhs.is_const() && rhs.is_const(),
            },
            Formula::Or(fs) | Formula::And(fs) => fs.iter().all(Self::is_ground),
            Formula::Not(f) => f.is_ground(),
        }
    }

    /// Returns the negation normal form of this formula.
    pub fn to_nnf(&self) -> NNFFormula {
        match self {
            Formula::Atom(a) => NNFFormula::Literal(Literal::Pos(a.clone())),
            Formula::Or(fs) => NNFFormula::Or(fs.iter().map(|f| f.to_nnf()).collect()),
            Formula::And(fs) => NNFFormula::And(fs.iter().map(|f| f.to_nnf()).collect()),
            Formula::Not(f) => match f.as_ref() {
                Formula::Atom(a) => NNFFormula::Literal(Literal::Neg(a.clone())),
                // Apply De Morgan's laws
                Formula::Or(fs) => NNFFormula::And(
                    fs.iter()
                        .map(|f| Formula::not(f.clone()).to_nnf())
                        .collect(),
                ),
                // Apply De Morgan's laws
                Formula::And(fs) => NNFFormula::Or(
                    fs.iter()
                        .map(|f| Formula::not(f.clone()).to_nnf())
                        .collect(),
                ),
                // Double negation, remove it
                Formula::Not(ff) => ff.to_nnf(),
            },
        }
    }
}

/// A first-order formula without quantifiers in *negation normal form*.
/// A nnf formula is inductive defined as follows:
/// - A [Literal] is a formula
/// - If `f` and `g` are formulas, then `f ∧ g` ([Formula::And]) and `f ∨ g` ([Formula::Or]) are formulas
///
/// A NNF formulas should not be constructed directly but instead using [Formula::to_nnf].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NNFFormula {
    /// A literal
    Literal(Literal),
    /// A disjunction
    Or(Vec<NNFFormula>),
    /// A conjunction
    And(Vec<NNFFormula>),
}

impl NNFFormula {
    pub fn literals(&self) -> Vec<&Literal> {
        match self {
            NNFFormula::Literal(l) => vec![l],
            NNFFormula::Or(fs) | NNFFormula::And(fs) => fs
                .iter()
                .map(NNFFormula::literals)
                .fold(Vec::new(), |acc, x| acc.into_iter().chain(x).collect()),
        }
    }

    pub fn asserted_literals(&self) -> Vec<&Literal> {
        match self {
            NNFFormula::Literal(l) => vec![l],
            NNFFormula::And(fs) => fs
                .iter()
                .map(NNFFormula::literals)
                .fold(Vec::new(), |acc, x| acc.into_iter().chain(x).collect()),
            NNFFormula::Or(_) => vec![],
        }
    }

    pub fn boolvar(var: Variable, sign: bool) -> Self {
        if sign {
            Self::Literal(Literal::Pos(Atom::BoolVar(var)))
        } else {
            Self::Literal(Literal::Neg(Atom::BoolVar(var)))
        }
    }
}

impl From<NNFFormula> for Formula {
    fn from(value: NNFFormula) -> Self {
        match value {
            NNFFormula::Literal(l) => match l {
                Literal::Pos(a) => Formula::Atom(a),
                Literal::Neg(a) => Formula::not(Formula::Atom(a)),
            },
            NNFFormula::Or(ors) => Formula::or(ors.into_iter().map(Formula::from).collect()),
            NNFFormula::And(ands) => Formula::and(ands.into_iter().map(Formula::from).collect()),
        }
    }
}

impl From<Formula> for NNFFormula {
    fn from(value: Formula) -> Self {
        value.to_nnf()
    }
}

/* Substitution and Evaluation */

impl Substitutable for Formula {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        match self {
            Formula::Atom(Atom::True) => Formula::ttrue(),
            Formula::Atom(Atom::False) => Formula::ffalse(),
            Formula::Atom(Atom::BoolVar(v)) => {
                if let Some(Term::Bool(f)) = sub.get(v) {
                    return f.as_ref().clone();
                } else {
                    Formula::Atom(Atom::BoolVar(v.clone()))
                }
            }
            Formula::Atom(Atom::Predicate(p)) => {
                Formula::Atom(Atom::Predicate(p.apply_substitution(sub)))
            }
            Formula::Or(fs) => Formula::or(fs.iter().map(|f| f.apply_substitution(sub)).collect()),
            Formula::And(fs) => {
                Formula::and(fs.iter().map(|f| f.apply_substitution(sub)).collect())
            }
            Formula::Not(f) => Formula::not(f.apply_substitution(sub)),
        }
    }
}

impl Alphabet for Formula {
    /// Returns the alphabet of constants used in this formula.
    /// Collects the alphabet of all predicates occurring in this formula and returns the union of them.
    /// See [Predicate] for more information.
    fn alphabet(&self) -> IndexSet<char> {
        match self {
            Formula::Atom(a) => a.alphabet(),
            Formula::Or(fs) | Formula::And(fs) => fs
                .iter()
                .map(Self::alphabet)
                .fold(IndexSet::new(), |acc, x| acc.union(&x).cloned().collect()),
            Formula::Not(f) => f.alphabet(),
        }
    }
}

impl Alphabet for NNFFormula {
    fn alphabet(&self) -> IndexSet<char> {
        self.literals().iter().fold(IndexSet::new(), |acc, x| {
            acc.union(&x.atom().alphabet()).cloned().collect()
        })
    }
}

impl Alphabet for Atom {
    fn alphabet(&self) -> IndexSet<char> {
        match self {
            Atom::Predicate(p) => p.alphabet(),
            Atom::BoolVar(_) => indexset! {},
            Atom::True => indexset! {},
            Atom::False => indexset! {},
        }
    }
}

impl Alphabet for Predicate {
    fn alphabet(&self) -> IndexSet<char> {
        match self {
            Predicate::Equality(Term::String(lhs), Term::String(rhs))
            | Predicate::Geq(Term::String(lhs), Term::String(rhs))
            | Predicate::Greater(Term::String(lhs), Term::String(rhs))
            | Predicate::Leq(Term::String(lhs), Term::String(rhs))
            | Predicate::Less(Term::String(lhs), Term::String(rhs)) => {
                let mut alphabet = lhs.alphabet();
                alphabet.extend(rhs.alphabet());
                alphabet
            }
            Predicate::In(Term::String(lhs), Term::Regular(rhs)) => {
                let mut alphabet = lhs.alphabet();
                alphabet.extend(rhs.alphabet());
                alphabet
            }
            _ => indexset! {},
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

impl Evaluable for Formula {
    fn eval(&self, sub: &Substitution) -> Option<bool> {
        match self {
            Formula::Atom(Atom::True) => Some(true),
            Formula::Atom(Atom::False) => Some(false),
            Formula::Atom(Atom::Predicate(p)) => p.eval(sub),
            Formula::Atom(Atom::BoolVar(x)) => match sub.get(x) {
                Some(Term::Bool(b)) => b.eval(sub),
                _ => None,
            },
            Formula::Or(fs) => {
                let mut is_falses = true;
                for f in fs {
                    match f.eval(&Substitution::new()) {
                        Some(true) => return Some(true),
                        Some(false) => (),
                        None => is_falses = false,
                    }
                }
                if is_falses {
                    Some(false)
                } else {
                    None
                }
            }
            Formula::And(fs) => {
                let mut is_true = true;
                for f in fs {
                    match f.eval(&Substitution::new()) {
                        Some(false) => return Some(false),
                        Some(true) => (),
                        None => is_true = false,
                    }
                }
                if is_true {
                    Some(true)
                } else {
                    None
                }
            }
            Formula::Not(f) => match f.eval(&Substitution::new()) {
                Some(true) => Some(false),
                Some(false) => Some(true),
                None => None,
            },
        }
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
                    (Some(l), Some(r)) => l >= r,
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
                    (Some(l), Some(r)) => l > r,
                    (_, _) => return None,
                }
            }
            Predicate::Greater(l, r) => {
                panic!("> unsupported for sorts {} and {}", l.sort(), r.sort())
            }
            Predicate::In(Term::String(p), Term::Regular(re)) => {
                if let Some(v) = p.apply_substitution(sub).is_const() {
                    let regex = match Regex::<char>::try_from(re.clone()) {
                        Ok(r) => r,
                        Err(e) => {
                            log::error!("Error while parsing regex: {}", e);
                            return None;
                        }
                    };
                    regex.contains(&v)
                } else {
                    return None;
                }
            }
            Predicate::In(_, _) => {
                panic!(
                    "`in` unsupported for sorts {} and {}",
                    self.signature()[0],
                    self.signature()[1]
                )
            }
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

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Pos(a) => write!(f, "{}", a),
            Literal::Neg(a) => write!(f, "¬({})", a),
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

impl Display for NNFFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Formula::from(self.clone()).fmt(f)
    }
}

/* Arbitrary */

impl Arbitrary for Atom {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if g.size() <= 1 {
            let v = Atom::BoolVar(Variable::new(String::arbitrary(g), Sort::Bool));
            g.choose(&[Atom::True, Atom::False, v]).unwrap().clone()
        } else {
            match g.choose(&[0, 1, 2, 3]) {
                Some(0) => Atom::Predicate(Predicate::arbitrary(g)),
                Some(1) => Atom::BoolVar(Variable::new(String::arbitrary(g), Sort::Bool)),
                Some(2) => Atom::True,
                Some(3) => Atom::False,
                _ => unreachable!(),
            }
        }
    }
}

impl Arbitrary for Predicate {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match g.choose(&[0, 1, 2, 3, 4, 5]) {
            Some(0) => Predicate::Equality(Term::arbitrary(g), Term::arbitrary(g)),
            Some(1) => Predicate::Leq(Term::arbitrary(g), Term::arbitrary(g)),
            Some(2) => Predicate::Less(Term::arbitrary(g), Term::arbitrary(g)),
            Some(3) => Predicate::Geq(Term::arbitrary(g), Term::arbitrary(g)),
            Some(4) => Predicate::Greater(Term::arbitrary(g), Term::arbitrary(g)),
            Some(5) => Predicate::In(Term::arbitrary(g), Term::arbitrary(g)),
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for Formula {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if g.size() <= 1 {
            Formula::Atom(Atom::arbitrary(g))
        } else {
            let mut newgen = quickcheck::Gen::new(g.size().saturating_sub(1));

            match g.choose(&[0, 1, 2, 3]) {
                Some(0) => {
                    let mut newgen = quickcheck::Gen::new(g.size().saturating_sub(1));
                    Formula::Atom(Atom::arbitrary(&mut newgen))
                }
                Some(1) => {
                    let mut newgen = quickcheck::Gen::new(g.size().saturating_div(2));
                    Formula::Or(vec![
                        Formula::arbitrary(&mut newgen),
                        Formula::arbitrary(&mut newgen),
                    ])
                }
                Some(2) => {
                    let mut newgen = quickcheck::Gen::new(g.size().saturating_div(2));
                    Formula::And(vec![
                        Formula::arbitrary(&mut newgen),
                        Formula::arbitrary(&mut newgen),
                    ])
                }
                Some(3) => Formula::Not(Box::new(Formula::arbitrary(&mut newgen))),
                _ => unreachable!(),
            }
        }
    }
}

#[cfg(test)]
mod test {

    use quickcheck_macros::quickcheck;

    use super::*;

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

    #[test]
    fn test_to_nnf_true() {
        let formula = Formula::ttrue();

        assert_eq!(
            formula.to_nnf(),
            NNFFormula::Literal(Literal::Pos(Atom::True))
        );
    }

    #[test]
    fn test_to_nnf_false() {
        let formula = Formula::ffalse();
        assert_eq!(
            formula.to_nnf(),
            NNFFormula::Literal(Literal::Pos(Atom::False))
        );
    }

    #[quickcheck]
    fn test_to_nnf_predicate(p: Predicate) {
        let atom = Atom::Predicate(p);
        let formula = Formula::Atom(atom.clone());
        assert_eq!(formula.to_nnf(), NNFFormula::Literal(Literal::Pos(atom)));
    }

    #[test]

    fn test_to_nnf_bool_var() {
        let atom = Atom::BoolVar(Variable::new(String::from("x"), Sort::Bool));
        let formula = Formula::Atom(atom.clone());
        assert_eq!(formula.to_nnf(), NNFFormula::Literal(Literal::Pos(atom)));
    }

    #[quickcheck]
    fn test_to_nnf_or(p1: Predicate, p2: Predicate) {
        let formula = Formula::not(Formula::or(vec![
            Formula::predicate(p1.clone()),
            Formula::predicate(p2.clone()),
        ]));

        let expected = NNFFormula::And(vec![
            NNFFormula::Literal(Literal::Neg(Atom::Predicate(p1))),
            NNFFormula::Literal(Literal::Neg(Atom::Predicate(p2))),
        ]);
        assert_eq!(formula.to_nnf(), expected);
    }

    #[quickcheck]
    fn test_to_nnf_and(p1: Predicate, p2: Predicate) {
        let formula = Formula::not(Formula::and(vec![
            Formula::predicate(p1.clone()),
            Formula::predicate(p2.clone()),
        ]));

        let expected = NNFFormula::Or(vec![
            NNFFormula::Literal(Literal::Neg(Atom::Predicate(p1))),
            NNFFormula::Literal(Literal::Neg(Atom::Predicate(p2))),
        ]);
        assert_eq!(formula.to_nnf(), expected);
    }

    #[quickcheck]
    fn test_to_nff_double_negations(p: Predicate) {
        let formula = Formula::not(Formula::not(Formula::predicate(p.clone())));
        assert_eq!(
            formula.to_nnf(),
            NNFFormula::Literal(Literal::Pos(Atom::Predicate(p)))
        );
    }
}
