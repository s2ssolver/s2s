use std::{collections::HashMap, fmt::Display, ops::Index};

use crate::model::words::Symbol;

use super::{words::WordEquation, Variable};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntArithTerm {
    Var(Variable),
    Const(isize),
    Plus(Box<IntArithTerm>, Box<IntArithTerm>),
    Times(Box<IntArithTerm>, Box<IntArithTerm>),
}

impl IntArithTerm {
    pub fn var(x: &Variable) -> Self {
        Self::Var(x.clone())
    }

    pub fn constant(c: isize) -> Self {
        Self::Const(c)
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
            IntArithTerm::Var(v) => {
                IntArithTerm::times(&IntArithTerm::constant(-1), &IntArithTerm::var(v))
            }
            IntArithTerm::Const(c) => IntArithTerm::constant(-c),
            IntArithTerm::Plus(x, y) => IntArithTerm::plus(&x.neg(), &y.neg()),
            IntArithTerm::Times(x, y) => IntArithTerm::times(&x.neg(), y),
        }
    }
}

impl Display for IntArithTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntArithTerm::Var(x) => write!(f, "{}", x),
            IntArithTerm::Const(c) => write!(f, "{}", c),
            IntArithTerm::Plus(x, y) => write!(f, "({} + {})", x, y),
            IntArithTerm::Times(x, y) => write!(f, "({} * {})", x, y),
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
    terms: Vec<LinearArithFactor>,
}

impl LinearArithTerm {
    pub fn new() -> Self {
        Self { terms: vec![] }
    }

    pub fn from_var(x: &Variable) -> Self {
        Self {
            terms: vec![LinearArithFactor::VarCoeff(x.clone(), 1)],
        }
    }

    pub fn from_const(c: isize) -> Self {
        Self {
            terms: vec![LinearArithFactor::Const(c)],
        }
    }

    pub fn add_factor(&mut self, f: LinearArithFactor) {
        self.terms.push(f);
    }

    pub fn add_var_coeff(&mut self, x: &Variable, c: isize) {
        self.terms.push(LinearArithFactor::VarCoeff(x.clone(), c));
    }

    pub fn extend(&mut self, other: Self) {
        self.terms.extend(other.terms);
    }

    pub fn iter(&self) -> impl Iterator<Item = &LinearArithFactor> {
        self.terms.iter()
    }

    /// The number of summands in the term
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Normalize the term by combining all coefficients of the same variable.
    /// After calling this, there is at most one factor per variable and at most one constant.
    pub fn normalize(&mut self) {
        let mut factors = HashMap::new();
        let mut residual = 0;
        for f in self.terms.iter() {
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
        self.terms.clear();
        for (x, c) in factors {
            self.terms.push(LinearArithFactor::VarCoeff(x, c));
        }
        if residual != 0 {
            self.terms.push(LinearArithFactor::Const(residual));
        }
    }

    /// Convert an integer arithmetic term to a linear arithmetic term.
    /// Returns `None` if the term is not linear, i.e., if it contains a product of two variables.
    pub fn from_int_arith_term(t: &IntArithTerm) -> Option<Self> {
        match t {
            IntArithTerm::Var(x) => Some(Self::from_var(x)),
            IntArithTerm::Const(c) => Some(Self::from_const(*c)),
            IntArithTerm::Plus(x, y) => {
                let mut res = Self::from_int_arith_term(x)?;
                res.extend(Self::from_int_arith_term(y)?);
                Some(res)
            }
            IntArithTerm::Times(x, y) => {
                let res_x = Self::from_int_arith_term(x)?;
                let res_y = Self::from_int_arith_term(y)?;
                // Distribute x over y, abort if non-linear
                let mut res = Self::new();
                for xx in res_x.iter() {
                    for yy in res_y.iter() {
                        match (yy, xx) {
                            (
                                LinearArithFactor::VarCoeff(_, _),
                                LinearArithFactor::VarCoeff(_, _),
                            ) => return None,
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
                Some(res)
            }
        }
    }

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
        &self.terms[index]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn from_linear_arith_term(
        lhs: &LinearArithTerm,
        rhs: &LinearArithTerm,
        typ: LinearConstraintType,
    ) -> Self {
        if let Some(c) = rhs.is_constant() {
            let mut lhs = lhs.clone();
            lhs.normalize();
            Self { lhs, rhs: c, typ }
        } else {
            let mut lhs = lhs.subtract(rhs);
            lhs.normalize();
            Self { lhs, rhs: 0, typ }
        }
    }

    pub fn lhs(&self) -> &LinearArithTerm {
        &self.lhs
    }
}

/* Pretty Printing */

impl Display for LinearArithTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for t in self.terms.iter() {
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

// TODO: Needs testing!
