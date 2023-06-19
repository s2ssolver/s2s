use quickcheck::{Arbitrary, Gen};

use crate::model::words::Symbol;
use std::{collections::HashMap, fmt::Display, ops::Index};

use super::{
    formula::Term, words::WordEquation, Evaluable, Sort, Substitutable, Substitution, Variable,
};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LinearArithFactor {
    VarCoeff(Variable, isize),
    Const(isize),
}

impl Display for LinearArithFactor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearArithFactor::VarCoeff(x, c) => {
                if *c == 1 {
                    write!(f, "{}", x)
                } else {
                    write!(f, "{}*{}", c, x)
                }
            }
            LinearArithFactor::Const(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub struct LinearArithTerm {
    factors: Vec<LinearArithFactor>,
}

impl LinearArithTerm {
    pub fn new() -> Self {
        Self { factors: vec![] }
    }

    pub fn from_var(x: &Variable) -> Self {
        Self {
            factors: vec![LinearArithFactor::VarCoeff(x.clone(), 1)],
        }
    }

    pub fn remove_factor(&mut self, f: &LinearArithFactor) -> bool {
        if let Some(index) = self.factors.iter().position(|x| *x == *f) {
            self.factors.remove(index);
            true
        } else {
            false
        }
    }

    /// Create a linear arithmetic term from a constant
    pub fn from_const(c: isize) -> Self {
        Self {
            factors: vec![LinearArithFactor::Const(c)],
        }
    }

    pub fn add_factor(&mut self, f: LinearArithFactor) {
        self.factors.push(f);
    }

    pub fn add_var_coeff(&mut self, x: &Variable, c: isize) {
        self.factors.push(LinearArithFactor::VarCoeff(x.clone(), c));
    }

    pub fn extend(&mut self, other: Self) {
        self.factors.extend(other.factors);
    }

    pub fn iter(&self) -> impl Iterator<Item = &LinearArithFactor> {
        self.factors.iter()
    }

    /// The number of summands in the term
    pub fn len(&self) -> usize {
        self.factors.len()
    }

    pub fn is_empty(&self) -> bool {
        self.factors.is_empty()
    }

    /// Normalize the term by combining all coefficients of the same variable.
    /// After calling this, there is at most one factor per variable and at most one constant.
    pub fn normalize(&mut self) {
        let mut factors = HashMap::new();
        let mut residual = 0;
        for f in self.factors.iter() {
            match f {
                LinearArithFactor::VarCoeff(x, c) => {
                    let entry = factors.entry(x.clone()).or_insert(0);
                    *entry += c;
                }
                LinearArithFactor::Const(c) => {
                    residual += c;
                }
            }
        }
        self.factors.clear();
        for (x, c) in factors {
            self.factors.push(LinearArithFactor::VarCoeff(x, c));
        }
        if residual != 0 {
            self.factors.push(LinearArithFactor::Const(residual));
        }
    }

    /// Convert an integer arithmetic term to a linear arithmetic term.

    pub fn subtract(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for f in other.iter() {
            match f {
                LinearArithFactor::VarCoeff(x, c) => {
                    res.add_factor(LinearArithFactor::VarCoeff(x.clone(), -c));
                }
                LinearArithFactor::Const(c) => {
                    res.add_factor(LinearArithFactor::Const(-c));
                }
            }
        }
        res
    }

    /// Returns `Some(c)` if the term is constant `c`, `None` otherwise.
    pub fn is_constant(&self) -> Option<isize> {
        let mut c = 0;
        for f in self.iter() {
            match f {
                LinearArithFactor::VarCoeff(_, _) => return None,
                LinearArithFactor::Const(c2) => c += c2,
            }
        }
        Some(c)
    }
}

impl Index<usize> for LinearArithTerm {
    type Output = LinearArithFactor;

    fn index(&self, index: usize) -> &Self::Output {
        &self.factors[index]
    }
}

impl From<IntTerm> for LinearArithTerm {
    fn from(value: IntTerm) -> Self {
        match value {
            IntTerm::Var(x) => Self::from_var(&x),
            IntTerm::Const(c) => Self::from_const(c),
            IntTerm::Plus(x, y) => {
                let mut res = Self::from(*x);
                res.extend(Self::from(*y));
                res
            }
            IntTerm::Times(x, y) => {
                let res_x = Self::from(*x);
                let res_y = Self::from(*y);
                // Distribute x over y, abort if non-linear
                let mut res = Self::new();
                for xx in res_x.iter() {
                    for yy in res_y.iter() {
                        match (yy, xx) {
                            (
                                LinearArithFactor::VarCoeff(_, _),
                                LinearArithFactor::VarCoeff(_, _),
                            ) => panic!("Non-linear constraint"),
                            (LinearArithFactor::Const(c2), LinearArithFactor::VarCoeff(v, c1))
                            | (LinearArithFactor::VarCoeff(v, c1), LinearArithFactor::Const(c2)) => {
                                res.add_factor(LinearArithFactor::VarCoeff(v.clone(), c1 * c2));
                            }
                            (LinearArithFactor::Const(c1), LinearArithFactor::Const(c2)) => {
                                res.add_factor(LinearArithFactor::Const(c1 * c2));
                            }
                        }
                    }
                }
                res
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LinearConstraintType {
    Eq,
    Leq,
    Less,
    Geq,
    Greater,
}

/// A linear constraint
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LinearConstraint {
    pub lhs: LinearArithTerm,
    pub rhs: isize,
    pub typ: LinearConstraintType,
}

impl LinearConstraint {
    /// Derive a linear constraint from a word equation
    pub fn from_word_equation(eq: &WordEquation) -> Self {
        let mut lhs = LinearArithTerm::new();
        let mut rhs = 0;
        for x in eq.variables() {
            let xs = &Symbol::Variable(x.clone());
            let coeff = eq.lhs().count(xs) as isize - eq.rhs().count(xs) as isize;
            lhs.add_var_coeff(&x.len_var(), coeff);
        }
        for c in eq.alphabet() {
            let c = &Symbol::Constant(c);
            let diff = eq.rhs().count(c) as isize - eq.lhs().count(c) as isize;
            rhs += diff;
        }

        Self {
            lhs,
            rhs,
            typ: LinearConstraintType::Eq,
        }
    }

    pub fn lhs(&self) -> &LinearArithTerm {
        &self.lhs
    }

    pub fn rhs(&self) -> isize {
        self.rhs
    }
}

impl From<(LinearArithTerm, LinearArithTerm, LinearConstraintType)> for LinearConstraint {
    fn from(value: (LinearArithTerm, LinearArithTerm, LinearConstraintType)) -> Self {
        let lhs = value.0;
        let rhs = value.1;
        let typ = value.2;
        if let Some(mut c) = rhs.is_constant() {
            let mut lhs = lhs;
            lhs.normalize();
            let mut consts = vec![];
            for fac in lhs.iter() {
                match fac {
                    LinearArithFactor::VarCoeff(_, _) => {}
                    LinearArithFactor::Const(c2) => {
                        consts.push(fac.clone());
                        c -= c2;
                    }
                }
            }
            for fac in consts {
                lhs.remove_factor(&fac);
            }

            Self { lhs, rhs: c, typ }
        } else {
            let mut lhs = lhs.subtract(&rhs);
            lhs.normalize();
            let mut consts = vec![];
            let mut c = 0;
            for fac in lhs.iter() {
                match fac {
                    LinearArithFactor::VarCoeff(_, _) => {}
                    LinearArithFactor::Const(c2) => {
                        consts.push(fac.clone());
                        c -= c2;
                    }
                }
            }
            for fac in consts {
                lhs.remove_factor(&fac);
            }

            Self { lhs, rhs: 0, typ }
        }
    }
}

impl Substitutable for LinearArithTerm {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        let mut res = Self::new();
        for f in self.iter() {
            match f {
                LinearArithFactor::VarCoeff(x, c) => {
                    let mut t = IntTerm::var(x);
                    t = IntTerm::times(&IntTerm::constant(*c), &t);
                    t = t.apply_substitution(sub);
                    res.extend(Self::from(t));
                }
                LinearArithFactor::Const(c) => {
                    res.add_factor(LinearArithFactor::Const(*c));
                }
            }
        }
        res
    }
}

impl Substitutable for LinearConstraint {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        Self {
            lhs: self.lhs.apply_substitution(sub),
            rhs: self.rhs,
            typ: self.typ,
        }
    }
}

impl Evaluable for LinearConstraint {
    fn eval(&self, sub: &Substitution) -> Option<bool> {
        let lhs = self.lhs.apply_substitution(sub);
        let rhs = self.rhs;
        let typ = self.typ;
        let lhs = lhs.is_constant()?;
        match typ {
            LinearConstraintType::Eq => Some(lhs == rhs),
            LinearConstraintType::Leq => Some(lhs <= rhs),
            LinearConstraintType::Less => Some(lhs < rhs),
            LinearConstraintType::Geq => Some(lhs >= rhs),
            LinearConstraintType::Greater => Some(lhs > rhs),
        }
    }
}

/* Pretty Printing */

impl Display for LinearArithTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for t in self.factors.iter() {
            if !first {
                write!(f, " + ")?;
            }
            write!(f, "{}", t)?;
            first = false;
        }
        Ok(())
    }
}

impl Display for LinearConstraintType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearConstraintType::Eq => write!(f, "="),
            LinearConstraintType::Leq => write!(f, "<="),
            LinearConstraintType::Less => write!(f, "<"),
            LinearConstraintType::Geq => write!(f, ">="),
            LinearConstraintType::Greater => write!(f, ">"),
        }
    }
}

impl Display for LinearConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.typ, self.rhs)
    }
}

/* Arbitrary */

impl Arbitrary for IntTerm {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        if g.size() <= 1 {
            g.choose(&[
                IntTerm::Const(isize::arbitrary(&mut Gen::new(1))),
                IntTerm::Var(Variable::new(
                    String::arbitrary(&mut Gen::new(1)),
                    Sort::Int,
                )),
            ]);
        }
        match g.choose(&[0, 1, 2, 3]) {
            Some(0) => IntTerm::Var(Variable::new(String::arbitrary(g), Sort::Int)),
            Some(1) => IntTerm::Const(isize::arbitrary(g)),
            Some(2) => IntTerm::Plus(
                Box::new(IntTerm::arbitrary(g)),
                Box::new(IntTerm::arbitrary(g)),
            ),
            Some(3) => IntTerm::Times(
                Box::new(IntTerm::arbitrary(g)),
                Box::new(IntTerm::arbitrary(g)),
            ),
            _ => unreachable!(),
        }
    }
}

// TODO: Needs testing!
