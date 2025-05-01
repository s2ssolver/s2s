use std::{fmt::Display, ops::Index, rc::Rc};

use indexmap::{IndexMap, IndexSet};
use quickcheck::Arbitrary;

use crate::context::{Sort, Sorted, Variable};

/// Represents different types of variable-based terms in a linear expression.
/// This enum differentiates between a simple variable and the length of a string variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VariableTerm {
    Int(Rc<Variable>), // A simple variable like x
    Len(Rc<Variable>), // Represents |x|, the length of a string variable
}
impl VariableTerm {
    pub fn is_len(&self) -> bool {
        matches!(self, VariableTerm::Len(_))
    }

    pub fn is_int(&self) -> bool {
        matches!(self, VariableTerm::Int(_))
    }

    pub fn variable(&self) -> &Rc<Variable> {
        match self {
            VariableTerm::Int(x) => x,
            VariableTerm::Len(x) => x,
        }
    }
}
impl Display for VariableTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariableTerm::Int(x) => write!(f, "{}", x),
            VariableTerm::Len(x) => write!(f, "|{}|", x),
        }
    }
}

/// Represents a single summand in a linear expression.
/// A `LinearSummand` can either be a scaled variable term or a constant value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Monomial {
    /// Multiply a variable term with a constant
    Mult(VariableTerm, i64),
    /// A constant
    Const(i64),
}

impl Monomial {
    /// Create a linear summand from a constant value
    pub fn constant(n: i64) -> Self {
        Monomial::Const(n)
    }

    /// Create a linear summand from a scaled integer variable
    pub fn int_variable(x: Rc<Variable>, c: i64) -> Self {
        assert!(x.sort().is_int(), "Variable must be of sort int");
        Monomial::Mult(VariableTerm::Int(x), c)
    }

    /// Create a linear summand from a scaled length variable
    pub fn len_variable(x: Rc<Variable>, c: i64) -> Self {
        assert!(x.sort().is_string(), "Variable must be of sort string");
        Monomial::Mult(VariableTerm::Len(x), c)
    }

    pub fn is_constant(&self) -> bool {
        match self {
            Monomial::Const(_) | Monomial::Mult(_, 0) => true, // 0*x = 0
            Monomial::Mult(_, _) => false,
        }
    }

    pub fn multiply(&self, c: i64) -> Self {
        match self {
            Monomial::Mult(x, c2) => Monomial::Mult(x.clone(), c * c2),
            Monomial::Const(c2) => Monomial::Const(c * c2),
        }
    }

    pub fn flip_sign(&self) -> Self {
        match self {
            Monomial::Mult(x, c) => Monomial::Mult(x.clone(), -c),
            Monomial::Const(c) => Monomial::Const(-c),
        }
    }
}

impl Display for Monomial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Monomial::Mult(x, c) => {
                if *c == 1 {
                    write!(f, "{}", x)
                } else {
                    write!(f, "{}*{}", c, x)
                }
            }
            Monomial::Const(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub struct LIATerm {
    factors: Vec<Monomial>,
    canonical: bool,
}

impl LIATerm {
    pub fn new() -> Self {
        Self {
            factors: vec![],
            canonical: true,
        }
    }

    /// Create a linear arithmetic term from ab (int or string) variable
    /// Panics if the variable is not of sort int or string
    pub fn from_var(x: Rc<Variable>) -> Self {
        match x.sort() {
            Sort::Int => Self {
                factors: vec![Monomial::Mult(VariableTerm::Int(x), 1)],
                canonical: true,
            },
            Sort::String => Self {
                factors: vec![Monomial::Mult(VariableTerm::Len(x), 1)],
                canonical: true,
            },
            _ => panic!("Variable must be of sort int or string"),
        }
    }

    /// Create a linear arithmetic term from the length of a string variable
    /// Panics if the variable is not of sort string
    pub fn from_var_len(x: Rc<Variable>) -> Self {
        assert!(x.sort().is_string(), "Variable must be of sort string");
        Self {
            factors: vec![Monomial::Mult(VariableTerm::Len(x), 1)],
            canonical: true,
        }
    }

    /// Create a linear arithmetic term from a constant
    pub fn from_const(c: i64) -> Self {
        Self {
            factors: vec![Monomial::Const(c)],
            canonical: true,
        }
    }

    /// Add a single summand to the term
    pub fn add_summand(&mut self, f: Monomial) {
        self.factors.push(f);
        self.canonical = false;
    }

    /// Multiplies every summand in the term with a constant
    pub fn multiply_constant(&mut self, c: i64) {
        for f in self.factors.iter_mut() {
            *f = f.multiply(c);
        }
        self.canonical = false;
    }

    /// Tries to muliply both terms and return the result.
    /// That only succeeds if the resulting term is linear.
    /// It is linear if and only if one side of the multiplication is a constant.
    /// If the multiplication is not linear, `None` is returned.
    pub fn multiply(left: Self, right: Self) -> Option<Self> {
        let mut res = LIATerm::new();
        for l in left.iter() {
            for r in right.iter() {
                // multiply l and r
                match (l, r) {
                    (Monomial::Mult(_, 0), Monomial::Mult(_, _))
                    | (Monomial::Mult(_, _), Monomial::Mult(_, 0)) => {
                        res.add_summand(Monomial::Const(0));
                    }
                    (Monomial::Mult(_, _), Monomial::Mult(_, _)) => {
                        return None;
                    }
                    (Monomial::Mult(x, c), Monomial::Const(s))
                    | (Monomial::Const(s), Monomial::Mult(x, c)) => {
                        res.add_summand(Monomial::Mult(x.clone(), c * s));
                    }
                    (Monomial::Const(s1), Monomial::Const(s2)) => {
                        res.add_summand(Monomial::Const(s1 * s2));
                    }
                }
            }
        }
        Some(res)
    }

    /// Add another linear term to this term
    pub fn add(&mut self, other: Self) {
        for smd in other.into_summands() {
            self.add_summand(smd);
        }
        self.canonical = false;
    }

    /// Subtract another linear term from this term
    pub fn sub(&mut self, other: Self) {
        for smd in other.into_summands() {
            match smd {
                Monomial::Mult(x, c) => {
                    self.add_summand(Monomial::Mult(x, -c));
                }
                Monomial::Const(c) => {
                    self.add_summand(Monomial::Const(-c));
                }
            }
        }
        self.canonical = false;
    }

    pub fn extend(&mut self, other: Self) {
        self.factors.extend(other.factors);
        self.canonical = false;
    }

    pub fn iter(&self) -> impl Iterator<Item = &Monomial> {
        self.factors.iter()
    }

    pub fn into_summands(self) -> impl Iterator<Item = Monomial> {
        self.factors.into_iter()
    }

    pub fn vars(&self) -> IndexSet<VariableTerm> {
        let mut vars = IndexSet::new();
        for f in self.iter() {
            match f {
                Monomial::Mult(x, _) => {
                    vars.insert(x.clone());
                }
                Monomial::Const(_) => {}
            }
        }
        vars
    }

    /// The number of summands in the term
    pub fn len(&self) -> usize {
        self.factors.len()
    }

    pub fn is_empty(&self) -> bool {
        self.factors.is_empty()
    }

    pub fn is_canonical(&self) -> bool {
        self.canonical
    }

    /// Canonicalizes the term by combining all coefficients of the same variable.
    /// After calling this, there is at most one factor per variable and at most one constant.
    pub fn canonicalize(&mut self) {
        if self.canonical {
            return;
        }
        let mut factors = IndexMap::new();
        let mut residual = 0;
        for f in self.factors.iter() {
            match f {
                Monomial::Mult(x, c) => {
                    let entry = factors.entry(x.clone()).or_insert(0);
                    *entry += c;
                }
                Monomial::Const(c) => {
                    residual += c;
                }
            }
        }
        self.factors.clear();
        for (x, c) in factors {
            if c != 0 {
                self.factors.push(Monomial::Mult(x, c));
            }
        }
        if residual != 0 {
            self.factors.push(Monomial::Const(residual));
        }
        self.canonical = true;
    }

    /// Convert an integer arithmetic term to a linear arithmetic term.
    pub fn subtract(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for f in other.iter() {
            match f {
                Monomial::Mult(x, c) => {
                    res.add_summand(Monomial::Mult(x.clone(), -c));
                }
                Monomial::Const(c) => {
                    res.add_summand(Monomial::Const(-c));
                }
            }
        }
        res
    }

    /// Returns `true` if the term is a single constant.
    /// Returns `false` otherwise.
    /// This does not check if the term can be reduced to a constant (e.g., `2 + 1`).
    /// See `reduce_constant` for that.
    pub fn is_constant(&self) -> bool {
        self.factors.len() == 1 && self.factors[0].is_constant()
    }

    /// Returns `Some(c)` if the term is constant `c`, `None` otherwise.
    pub fn as_constant(&self) -> Option<i64> {
        let mut c = 0;
        for f in self.iter() {
            match f {
                Monomial::Mult(_, 0) => (),
                Monomial::Mult(_, _) => return None,
                Monomial::Const(c2) => c += c2,
            }
        }
        Some(c)
    }

    /// Returns `Some(x)` if the term is a single variable `x`, `None` otherwise.
    pub fn as_variable(&self) -> Option<&Variable> {
        if self.factors.len() == 1 {
            match &self.factors[0] {
                Monomial::Mult(VariableTerm::Int(x), 1) => Some(x),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl Index<usize> for LIATerm {
    type Output = Monomial;

    fn index(&self, index: usize) -> &Self::Output {
        &self.factors[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LIAOp {
    Eq,
    Ineq,
    Leq,
    Less,
    Geq,
    Greater,
}
impl LIAOp {
    pub fn eval(&self, lhs: i64, rhs: i64) -> bool {
        match self {
            LIAOp::Eq => lhs == rhs,
            LIAOp::Ineq => lhs != rhs,
            LIAOp::Leq => lhs <= rhs,
            LIAOp::Less => lhs < rhs,
            LIAOp::Geq => lhs >= rhs,
            LIAOp::Greater => lhs > rhs,
        }
    }

    /// Flips the operator in case of an inequality.
    /// - `a < b` becomes `a > b`
    /// - `a <= b` becomes `a >= b`
    /// - `a > b` becomes `a < b`
    /// - `a >= b` becomes `a <= b`
    /// - `a = b` stays `a = b` and `a != b` stays `a != b`
    pub fn flip(&self) -> Self {
        match self {
            LIAOp::Eq => LIAOp::Eq,
            LIAOp::Ineq => LIAOp::Ineq,
            LIAOp::Leq => LIAOp::Geq,
            LIAOp::Less => LIAOp::Greater,
            LIAOp::Geq => LIAOp::Leq,
            LIAOp::Greater => LIAOp::Less,
        }
    }
}

/// A linear constraint
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LIAConstraint {
    lhs: LIATerm,
    rhs: i64,
    typ: LIAOp,
    is_canonical: bool,
}

impl LIAConstraint {
    pub fn new(lhs: LIATerm, typ: LIAOp, rhs: i64) -> Self {
        Self {
            lhs,
            rhs,
            typ,
            is_canonical: false,
        }
    }

    pub fn lhs(&self) -> &LIATerm {
        &self.lhs
    }
    pub fn rhs(&self) -> i64 {
        self.rhs
    }
    pub fn operator(&self) -> LIAOp {
        self.typ
    }

    pub(crate) fn variables(&self) -> IndexSet<Rc<Variable>> {
        let mut vars = IndexSet::new();
        for f in self.lhs.iter() {
            match f {
                Monomial::Mult(x, _) => {
                    vars.insert(x.variable().clone());
                }
                Monomial::Const(_) => {}
            }
        }
        vars
    }

    /// Negate the constraint.
    /// - `a = b` becomes `a != b`
    /// - `a != b` becomes `a = b`
    /// - `a <= b` becomes `a > b`
    /// - `a < b` becomes `a >= b`
    /// - `a >= b` becomes `a < b`
    /// - `a > b` becomes `a <= b`
    pub fn negate(&self) -> Self {
        let new_op = match self.typ {
            LIAOp::Eq => LIAOp::Ineq,
            LIAOp::Ineq => LIAOp::Eq,
            LIAOp::Leq => LIAOp::Greater,
            LIAOp::Less => LIAOp::Geq,
            LIAOp::Geq => LIAOp::Less,
            LIAOp::Greater => LIAOp::Leq,
        };
        let mut negated = LIAConstraint::new(self.lhs.clone(), new_op, self.rhs);
        negated.is_canonical = self.is_canonical;
        negated
    }

    pub fn is_canonical(&self) -> bool {
        self.is_canonical
    }

    pub fn canonicalize(&mut self) {
        if self.is_canonical {
            return;
        }
        self.lhs.canonicalize();
        let mut rhs_new = self.rhs;
        let mut lhs_new = LIATerm::new();
        for f in self.lhs.iter() {
            match f {
                Monomial::Mult(_, _) => lhs_new.add_summand(f.clone()),
                Monomial::Const(c) => rhs_new -= c,
            }
        }
        self.lhs = if lhs_new.is_empty() {
            LIATerm::from_const(0)
        } else {
            lhs_new
        };

        self.rhs = rhs_new;
        self.is_canonical = true;
    }
}

/* Pretty Printing */

impl Display for LIATerm {
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

impl Display for LIAOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LIAOp::Eq => write!(f, "="),
            LIAOp::Ineq => write!(f, "!="),
            LIAOp::Leq => write!(f, "<="),
            LIAOp::Less => write!(f, "<"),
            LIAOp::Geq => write!(f, ">="),
            LIAOp::Greater => write!(f, ">"),
        }
    }
}

impl Display for LIAConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.typ, self.rhs)
    }
}

// TODO: Needs testing!

impl Arbitrary for LIAOp {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match u8::arbitrary(g) % 6 {
            0 => LIAOp::Eq,
            1 => LIAOp::Ineq,
            2 => LIAOp::Leq,
            3 => LIAOp::Less,
            4 => LIAOp::Geq,
            5 => LIAOp::Greater,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn test_operator_flip_flip(op: LIAOp) -> bool {
        op.flip().flip() == op
    }
}
