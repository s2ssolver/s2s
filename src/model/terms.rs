use std::fmt::{Display, Formatter};

use indexmap::IndexSet;
use quickcheck::{Arbitrary, Gen};

use super::{
    constraints::Pattern,
    formula::{Alphabet, Formula, Sorted},
    Sort, Substitutable, Substitution, Variable,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    String(StringTerm),
    Int(IntTerm),
    Regular(ReTerm),
    Bool(Box<Formula>),
}

impl Term {
    pub fn is_const(&self) -> bool {
        match self {
            Term::String(s) => s.is_const().is_some(),
            Term::Int(i) => i.is_const().is_some(),
            Term::Regular(_) => todo!(),
            Term::Bool(f) => f.is_ground(),
        }
    }

    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            Term::String(s) => s.vars(),
            Term::Int(i) => i.vars(),
            Term::Regular(r) => r.vars(),
            Term::Bool(f) => f.as_ref().vars(),
        }
    }
}

impl Substitutable for Term {
    fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            Term::String(s) => Term::String(s.apply_substitution(subs)),
            Term::Int(i) => Term::Int(i.apply_substitution(subs)),
            Term::Regular(_r) => {
                if _r.is_grounded() {
                    self.clone()
                } else {
                    panic!("Ungrounded regular terms are not supported");
                }
            }
            Term::Bool(f) => Term::Bool(Box::new(f.apply_substitution(subs))),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StringTerm {
    Variable(Variable),
    Constant(Vec<char>),
    Concat(Box<StringTerm>, Box<StringTerm>),
}

impl Default for StringTerm {
    fn default() -> Self {
        Self::empty()
    }
}

impl Sorted for StringTerm {
    fn sort(&self) -> Sort {
        Sort::String
    }
}

impl StringTerm {
    /// The empty string
    pub fn empty() -> Self {
        Self::Constant(vec![])
    }

    pub fn is_const(&self) -> Option<Vec<char>> {
        match self {
            StringTerm::Constant(c) => Some(c.to_vec()),
            StringTerm::Variable(_) => None,
            StringTerm::Concat(x, y) => match (x.is_const(), y.is_const()) {
                (Some(x), Some(y)) => Some(x.iter().chain(y.iter()).cloned().collect()),
                _ => None,
            },
        }
    }

    pub fn reverse(&self) -> StringTerm {
        match self {
            StringTerm::Variable(var) => StringTerm::Variable(var.clone()),
            StringTerm::Constant(word) => {
                StringTerm::Constant(word.iter().rev().cloned().collect())
            }
            StringTerm::Concat(lhs, rhs) => StringTerm::concat(rhs.reverse(), lhs.reverse()),
        }
    }

    pub fn constant(str: &str) -> Self {
        Self::Constant(str.chars().collect())
    }

    pub fn variable(var: &Variable) -> Self {
        Self::Variable(var.clone())
    }

    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            StringTerm::Variable(var) => {
                let mut vars = IndexSet::new();
                vars.insert(var);
                vars
            }
            StringTerm::Constant(_) => IndexSet::new(),
            StringTerm::Concat(lhs, rhs) => lhs.vars().union(&rhs.vars()).cloned().collect(),
        }
    }

    pub fn concat(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (StringTerm::Constant(x), StringTerm::Constant(y)) => {
                StringTerm::Constant(x.iter().chain(y.iter()).cloned().collect())
            }
            (x, y) => StringTerm::Concat(Box::new(x), Box::new(y)),
        }
    }

    pub fn concat_const(lhs: Self, other: &str) -> Self {
        Self::concat(lhs, StringTerm::Constant(other.chars().collect()))
    }

    pub fn concat_var(lhs: Self, var: &Variable) -> Self {
        Self::concat(lhs, StringTerm::Variable(var.clone()))
    }

    pub fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            StringTerm::Variable(var) => {
                if let Some(term) = subs.get(var) {
                    match term {
                        Term::String(s) => s.clone(),
                        _ => panic!("Cannot substitute variable {} with term {}", var, term),
                    }
                } else {
                    self.clone()
                }
            }
            StringTerm::Constant(_) => self.clone(),
            StringTerm::Concat(lhs, rhs) => {
                StringTerm::concat(lhs.apply_substitution(subs), rhs.apply_substitution(subs))
            }
        }
    }
}

impl Alphabet for StringTerm {
    fn alphabet(&self) -> IndexSet<char> {
        match self {
            StringTerm::Variable(_) => IndexSet::new(),
            StringTerm::Constant(word) => word.iter().cloned().collect(),
            StringTerm::Concat(lhs, rhs) => {
                lhs.alphabet().union(&rhs.alphabet()).cloned().collect()
            }
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

impl From<ReTerm> for Term {
    fn from(r: ReTerm) -> Self {
        Term::Regular(r)
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

/// Represents a terms of sort lang that form regular languages.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReTerm {
    /// An empty language.
    None,
    /// The language containing any character.
    Any,
    /// The language containing all sequences of characters.
    All,
    /// The language containing the given string term.
    String(StringTerm),
    /// The language containing the finite union of the given languages.
    Union(Vec<ReTerm>),
    /// The language containing the concatenation of the given languages.
    Concat(Vec<ReTerm>),
    /// The Kleene closure of a language.
    Star(Box<ReTerm>),
    /// The positive closure of a language.
    Plus(Box<ReTerm>),
    /// The language containing the given language and the empty string.
    Optional(Box<ReTerm>),
    /// The language containing the finite intersection of the given languages.
    Inter(Vec<ReTerm>),
    /// The language containing the difference of the given languages.
    Diff(Box<ReTerm>, Box<ReTerm>),
    /// The language containing the complement of the given language.
    Comp(Box<ReTerm>),
    /// The language containing all words between the given bounds (inclusively).
    /// Is empty if the bounds are not constants of length 1.
    Range(StringTerm, StringTerm),
    /// The language containing all words of the given language raised to the given power.
    Pow(Box<ReTerm>, usize),
    /// The language containing all words of the given language repeated between the given bounds (inclusively).
    Loop(Box<ReTerm>, usize, usize),
}

impl ReTerm {
    /// Returns the alphabet of constants used to construct the term.
    /// Note that the alphabet of an ReTerm is not necessarily the same as the alphabet of the language denoted by it.
    /// For example, the rterm `ReTerm::All` denotes the language `T^*` over some alphabet T, but its alphabet of constants is empty.
    pub fn alphabet(&self) -> IndexSet<char> {
        match self {
            ReTerm::None => IndexSet::new(),
            ReTerm::Any => IndexSet::new(),
            ReTerm::All => IndexSet::new(),
            ReTerm::String(p) => p.alphabet(),
            ReTerm::Union(v) | ReTerm::Concat(v) | ReTerm::Inter(v) => {
                v.iter().flat_map(|r| r.alphabet()).collect()
            }
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _)
            | ReTerm::Loop(r, _, _) => r.alphabet(),
            ReTerm::Diff(r1, r2) => r1.alphabet().union(&r2.alphabet()).cloned().collect(),
            ReTerm::Range(p1, p2) => p1.alphabet().union(&p2.alphabet()).cloned().collect(),
        }
    }

    /// Checks whether the expression is grounded.
    /// Returns true if it does not contain variable symbols and false otherwise.
    pub fn is_grounded(&self) -> bool {
        match self {
            ReTerm::String(p) => p.is_const().is_some(),
            ReTerm::Union(v) | ReTerm::Concat(v) | ReTerm::Inter(v) => {
                v.iter().all(Self::is_grounded)
            }
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _)
            | ReTerm::Loop(r, _, _) => r.is_grounded(),
            ReTerm::Diff(r1, r2) => r1.is_grounded() && r2.is_grounded(),
            ReTerm::Range(p1, p2) => p1.is_const().is_some() && p2.is_const().is_some(),
            ReTerm::None => true,
            ReTerm::Any => true,
            ReTerm::All => true,
        }
    }

    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            ReTerm::String(p) => p.vars(),
            ReTerm::Union(v) | ReTerm::Concat(v) | ReTerm::Inter(v) => {
                v.iter().flat_map(|r| r.vars()).collect()
            }
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _)
            | ReTerm::Loop(r, _, _) => r.vars(),
            ReTerm::Diff(r1, r2) => r1.vars().union(&r2.vars()).cloned().collect(),
            ReTerm::Range(p1, p2) => p1.vars().union(&p2.vars()).cloned().collect(),
            _ => IndexSet::new(),
        }
    }

    /// Return true if the expression contains a loop.
    pub fn contains_loop(&self) -> bool {
        match self {
            ReTerm::Loop(_, _, _) => true,
            ReTerm::Union(v) | ReTerm::Concat(v) | ReTerm::Inter(v) => {
                v.iter().any(Self::contains_loop)
            }
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _) => r.contains_loop(),
            ReTerm::Diff(r1, r2) => r1.contains_loop() || r2.contains_loop(),
            ReTerm::Range(_, _) => false,
            _ => false,
        }
    }

    /// Return true if the expression contains an intersection.
    pub fn contains_inter(&self) -> bool {
        match self {
            ReTerm::Inter(_) => true,
            ReTerm::Union(v) | ReTerm::Concat(v) => v.iter().any(Self::contains_inter),
            ReTerm::Star(r)
            | ReTerm::Plus(r)
            | ReTerm::Optional(r)
            | ReTerm::Comp(r)
            | ReTerm::Pow(r, _)
            | ReTerm::Loop(r, _, _) => r.contains_inter(),
            ReTerm::Diff(r1, r2) => r1.contains_inter() || r2.contains_inter(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntTerm {
    Var(Variable),
    Const(isize),
    Plus(Box<IntTerm>, Box<IntTerm>),
    Times(Box<IntTerm>, Box<IntTerm>),
}

impl IntTerm {
    pub fn var(x: &Variable) -> Self {
        Self::Var(x.clone())
    }

    pub fn constant(c: isize) -> Self {
        Self::Const(c)
    }

    /// Returns `Some(c)` if the term is equal to constant value `c`, `None` otherwise.
    pub fn is_const(&self) -> Option<isize> {
        match self {
            IntTerm::Var(_) => None,
            IntTerm::Const(c) => Some(*c),
            IntTerm::Plus(a, b) => match (a.is_const(), b.is_const()) {
                (Some(c1), Some(c2)) => Some(c1 + c2),
                _ => None,
            },
            IntTerm::Times(a, b) => match (a.is_const(), b.is_const()) {
                (Some(c1), Some(c2)) => Some(c1 * c2),
                _ => None,
            },
        }
    }

    pub fn plus(x: &Self, y: &Self) -> Self {
        Self::Plus(Box::new(x.clone()), Box::new(y.clone()))
    }

    pub fn times(x: &Self, y: &Self) -> Self {
        Self::Times(Box::new(x.clone()), Box::new(y.clone()))
    }

    /// Negate the term
    pub fn neg(&self) -> Self {
        match self {
            IntTerm::Var(v) => IntTerm::times(&IntTerm::constant(-1), &IntTerm::var(v)),
            IntTerm::Const(c) => IntTerm::constant(-c),
            IntTerm::Plus(x, y) => IntTerm::plus(&x.neg(), &y.neg()),
            IntTerm::Times(x, y) => IntTerm::times(&x.neg(), y),
        }
    }

    pub fn vars(&self) -> IndexSet<&Variable> {
        match self {
            IntTerm::Var(x) => {
                let mut vars = IndexSet::new();
                vars.insert(x);
                vars
            }
            IntTerm::Const(_) => IndexSet::new(),
            IntTerm::Plus(x, y) => x.vars().union(&y.vars()).cloned().collect(),
            IntTerm::Times(x, y) => x.vars().union(&y.vars()).cloned().collect(),
        }
    }

    pub fn apply_substitution(&self, subs: &Substitution) -> Self {
        match self {
            IntTerm::Var(x) => match subs.get(x) {
                Some(Term::Int(t)) => t.clone(),
                // TODO: Return result
                Some(_) => panic!("Cannot substitute integer variable with string"),
                None => self.clone(),
            },
            IntTerm::Const(_) => self.clone(),
            IntTerm::Plus(x, y) => {
                IntTerm::plus(&x.apply_substitution(subs), &y.apply_substitution(subs))
            }
            IntTerm::Times(x, y) => {
                IntTerm::times(&x.apply_substitution(subs), &y.apply_substitution(subs))
            }
        }
    }
}

impl From<isize> for IntTerm {
    fn from(value: isize) -> Self {
        Self::Const(value)
    }
}

/* Pretty Printing */

impl Display for StringTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            StringTerm::Variable(var) => write!(f, "{}", var),
            StringTerm::Constant(word) => write!(f, "{}", word.iter().collect::<String>()),
            StringTerm::Concat(lhs, rhs) => write!(f, "{}{}", lhs, rhs),
        }
    }
}

impl Display for IntTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntTerm::Var(x) => write!(f, "{}", x),
            IntTerm::Const(c) => write!(f, "{}", c),
            IntTerm::Plus(x, y) => write!(f, "({} + {})", x, y),
            IntTerm::Times(x, y) => write!(f, "({} * {})", x, y),
        }
    }
}

impl Display for ReTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ReTerm::None => write!(f, "∅"),
            ReTerm::Any => write!(f, "?"),
            ReTerm::All => write!(f, "?*"),
            ReTerm::String(w) => write!(f, "{}", w),
            ReTerm::Union(rs) => write!(
                f,
                "({})",
                rs.iter()
                    .map(|r| format!("{}", r))
                    .collect::<Vec<String>>()
                    .join(" | ")
            ),
            ReTerm::Concat(rs) => write!(
                f,
                "{}",
                rs.iter()
                    .map(|r| format!("{}", r))
                    .collect::<Vec<String>>()
                    .join(" · ")
            ),
            ReTerm::Star(r) => write!(f, "{}*", r),
            ReTerm::Plus(r) => write!(f, "{}+", r),
            ReTerm::Optional(r) => write!(f, "({}?)", r),
            ReTerm::Inter(rs) => write!(
                f,
                "({})",
                rs.iter()
                    .map(|r| format!("{}", r))
                    .collect::<Vec<String>>()
                    .join(" ∩ ")
            ),
            ReTerm::Diff(r1, r2) => write!(f, r"({} \ {})", r1, r2),
            ReTerm::Comp(r) => write!(f, "{}'", r),
            ReTerm::Range(rl, ru) => write!(f, "[{}, {}]", rl, ru),
            ReTerm::Pow(r, e) => write!(f, "({}^{})", r, e),
            ReTerm::Loop(r, l, u) => write!(f, "({}^({}..{}))", r, l, u),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::String(t) => write!(f, "{}", t),
            Term::Int(t) => write!(f, "{}", t),
            Term::Bool(t) => write!(f, "{}", t),
            Term::Regular(r) => write!(f, "{}", r),
        }
    }
}

/* Arbitrary */

impl Arbitrary for Term {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match g.choose(&[0, 1, 2]) {
            // TODO regex terms
            Some(&0) => Term::Bool(Box::new(Formula::boolvar(Variable::new(
                String::arbitrary(g),
                Sort::Bool,
            )))),
            Some(&1) => Term::String(StringTerm::arbitrary(g)),
            Some(&2) => Term::Int(IntTerm::arbitrary(g)),
            Some(&3) => unreachable!(),
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for StringTerm {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        Pattern::arbitrary(g).into()
    }
}

impl Arbitrary for IntTerm {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if g.size() <= 1 {
            return g
                .choose(&[
                    IntTerm::Const(isize::arbitrary(&mut Gen::new(1))),
                    IntTerm::Var(Variable::new(
                        String::arbitrary(&mut Gen::new(1)),
                        Sort::Int,
                    )),
                ])
                .unwrap()
                .clone();
        }
        let mut new_gen = Gen::new(g.size() - 1);
        match g.choose(&[0, 1, 2, 3]) {
            Some(0) => IntTerm::Var(Variable::new(String::arbitrary(g), Sort::Int)),
            Some(1) => IntTerm::Const(isize::arbitrary(g)),
            Some(2) => IntTerm::Plus(
                Box::new(IntTerm::arbitrary(&mut new_gen)),
                Box::new(IntTerm::arbitrary(&mut new_gen)),
            ),
            Some(3) => IntTerm::Times(
                Box::new(IntTerm::arbitrary(&mut new_gen)),
                Box::new(IntTerm::arbitrary(&mut new_gen)),
            ),
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for ReTerm {
    fn arbitrary(g: &mut Gen) -> Self {
        let mut gen_log = Gen::new(g.size().saturating_div(2));
        let mut gen_dec = Gen::new(g.size().saturating_sub(1));
        let range = if g.size() <= 1 {
            vec![0, 1, 2, 3]
        } else {
            vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
        };
        match g.choose(&range).unwrap() {
            0 => ReTerm::All,
            1 => ReTerm::Any,
            2 => ReTerm::None,
            3 => ReTerm::String(StringTerm::arbitrary(&mut gen_dec)),
            4 => ReTerm::Union(vec![
                ReTerm::arbitrary(&mut gen_log),
                ReTerm::arbitrary(&mut gen_log),
            ]),
            5 => ReTerm::Concat(vec![
                ReTerm::arbitrary(&mut gen_log),
                ReTerm::arbitrary(&mut gen_log),
            ]),
            6 => ReTerm::Star(Box::new(ReTerm::arbitrary(&mut gen_dec))),
            7 => ReTerm::Plus(Box::new(ReTerm::arbitrary(&mut gen_dec))),
            8 => ReTerm::Optional(Box::new(ReTerm::arbitrary(&mut gen_dec))),
            9 => ReTerm::Inter(vec![
                ReTerm::arbitrary(&mut gen_log),
                ReTerm::arbitrary(&mut gen_log),
            ]),
            10 => ReTerm::Diff(
                Box::new(ReTerm::arbitrary(&mut gen_log)),
                Box::new(ReTerm::arbitrary(&mut gen_log)),
            ),
            11 => ReTerm::Comp(Box::new(ReTerm::arbitrary(&mut gen_dec))),
            12 => ReTerm::Range(
                StringTerm::arbitrary(&mut gen_log),
                StringTerm::arbitrary(&mut gen_log),
            ),
            13 => ReTerm::Pow(
                Box::new(ReTerm::arbitrary(&mut gen_dec)),
                usize::arbitrary(g),
            ),
            14 => ReTerm::Loop(
                Box::new(ReTerm::arbitrary(&mut gen_dec)),
                usize::arbitrary(g),
                usize::arbitrary(g),
            ),
            _ => unreachable!(),
        }
    }
}
