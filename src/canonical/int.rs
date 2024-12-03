use std::{collections::HashMap, fmt::Display, ops::Index, rc::Rc};

use indexmap::IndexSet;
use quickcheck::Arbitrary;

use crate::node::{Sort, Sorted, Variable};

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
pub enum LinearSummand {
    /// Multiply a variable term with a constant
    Mult(VariableTerm, i64),
    /// A constant
    Const(i64),
}

impl LinearSummand {
    /// Create a linear summand from a constant value
    pub fn constant(n: i64) -> Self {
        LinearSummand::Const(n)
    }

    /// Create a linear summand from a scaled integer variable
    pub fn int_variable(x: Rc<Variable>, c: i64) -> Self {
        assert!(x.sort().is_int(), "Variable must be of sort int");
        LinearSummand::Mult(VariableTerm::Int(x), c)
    }

    /// Create a linear summand from a scaled length variable
    pub fn len_variable(x: Rc<Variable>, c: i64) -> Self {
        assert!(x.sort().is_string(), "Variable must be of sort string");
        LinearSummand::Mult(VariableTerm::Len(x), c)
    }

    pub fn is_constant(&self) -> bool {
        match self {
            LinearSummand::Const(_) | LinearSummand::Mult(_, 0) => true, // 0*x = 0
            LinearSummand::Mult(_, _) => false,
        }
    }

    pub fn multiply(&self, c: i64) -> Self {
        match self {
            LinearSummand::Mult(x, c2) => LinearSummand::Mult(x.clone(), c * c2),
            LinearSummand::Const(c2) => LinearSummand::Const(c * c2),
        }
    }

    pub fn flip_sign(&self) -> Self {
        match self {
            LinearSummand::Mult(x, c) => LinearSummand::Mult(x.clone(), -c),
            LinearSummand::Const(c) => LinearSummand::Const(-c),
        }
    }
}

impl Display for LinearSummand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearSummand::Mult(x, c) => {
                if *c == 1 {
                    write!(f, "{}", x)
                } else {
                    write!(f, "{}*{}", c, x)
                }
            }
            LinearSummand::Const(c) => write!(f, "{}", c),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub struct LinearArithTerm {
    factors: Vec<LinearSummand>,
    canonical: bool,
}

impl LinearArithTerm {
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
                factors: vec![LinearSummand::Mult(VariableTerm::Int(x), 1)],
                canonical: true,
            },
            Sort::String => Self {
                factors: vec![LinearSummand::Mult(VariableTerm::Len(x), 1)],
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
            factors: vec![LinearSummand::Mult(VariableTerm::Len(x), 1)],
            canonical: true,
        }
    }

    /// Create a linear arithmetic term from a constant
    pub fn from_const(c: i64) -> Self {
        Self {
            factors: vec![LinearSummand::Const(c)],
            canonical: true,
        }
    }

    /// Add a single summand to the term
    pub fn add_summand(&mut self, f: LinearSummand) {
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
        let mut res = LinearArithTerm::new();
        for l in left.iter() {
            for r in right.iter() {
                // multiply l and r
                match (l, r) {
                    (LinearSummand::Mult(_, 0), LinearSummand::Mult(_, _))
                    | (LinearSummand::Mult(_, _), LinearSummand::Mult(_, 0)) => {
                        res.add_summand(LinearSummand::Const(0));
                    }
                    (LinearSummand::Mult(_, _), LinearSummand::Mult(_, _)) => {
                        return None;
                    }
                    (LinearSummand::Mult(x, c), LinearSummand::Const(s))
                    | (LinearSummand::Const(s), LinearSummand::Mult(x, c)) => {
                        res.add_summand(LinearSummand::Mult(x.clone(), c * s));
                    }
                    (LinearSummand::Const(s1), LinearSummand::Const(s2)) => {
                        res.add_summand(LinearSummand::Const(s1 * s2));
                    }
                }
            }
        }
        Some(res)
    }

    /// Add another linear term to this term
    pub fn add(&mut self, other: Self) {
        for smd in other.into_iter() {
            self.add_summand(smd);
        }
        self.canonical = false;
    }

    /// Subtract another linear term from this term
    pub fn sub(&mut self, other: Self) {
        for smd in other.into_iter() {
            match smd {
                LinearSummand::Mult(x, c) => {
                    self.add_summand(LinearSummand::Mult(x, -c));
                }
                LinearSummand::Const(c) => {
                    self.add_summand(LinearSummand::Const(-c));
                }
            }
        }
        self.canonical = false;
    }

    pub fn extend(&mut self, other: Self) {
        self.factors.extend(other.factors);
        self.canonical = false;
    }

    pub fn iter(&self) -> impl Iterator<Item = &LinearSummand> {
        self.factors.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = LinearSummand> {
        self.factors.into_iter()
    }

    pub fn vars(&self) -> IndexSet<VariableTerm> {
        let mut vars = IndexSet::new();
        for f in self.iter() {
            match f {
                LinearSummand::Mult(x, _) => {
                    vars.insert(x.clone());
                }
                LinearSummand::Const(_) => {}
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
        let mut factors = HashMap::new();
        let mut residual = 0;
        for f in self.factors.iter() {
            match f {
                LinearSummand::Mult(x, c) => {
                    let entry = factors.entry(x.clone()).or_insert(0);
                    *entry += c;
                }
                LinearSummand::Const(c) => {
                    residual += c;
                }
            }
        }
        self.factors.clear();
        for (x, c) in factors {
            if c != 0 {
                self.factors.push(LinearSummand::Mult(x, c));
            }
        }
        if residual != 0 {
            self.factors.push(LinearSummand::Const(residual));
        }
        self.canonical = true;
    }

    /// Convert an integer arithmetic term to a linear arithmetic term.
    pub fn subtract(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for f in other.iter() {
            match f {
                LinearSummand::Mult(x, c) => {
                    res.add_summand(LinearSummand::Mult(x.clone(), -c));
                }
                LinearSummand::Const(c) => {
                    res.add_summand(LinearSummand::Const(-c));
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
                LinearSummand::Mult(_, 0) => (),
                LinearSummand::Mult(_, _) => return None,
                LinearSummand::Const(c2) => c += c2,
            }
        }
        Some(c)
    }

    /// Returns `Some(x)` if the term is a single variable `x`, `None` otherwise.
    pub fn as_variable(&self) -> Option<&Variable> {
        if self.factors.len() == 1 {
            match &self.factors[0] {
                LinearSummand::Mult(VariableTerm::Int(x), 1) => Some(x),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl Index<usize> for LinearArithTerm {
    type Output = LinearSummand;

    fn index(&self, index: usize) -> &Self::Output {
        &self.factors[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOperator {
    Eq,
    Ineq,
    Leq,
    Less,
    Geq,
    Greater,
}
impl ArithOperator {
    pub fn eval(&self, lhs: i64, rhs: i64) -> bool {
        match self {
            ArithOperator::Eq => lhs == rhs,
            ArithOperator::Ineq => lhs != rhs,
            ArithOperator::Leq => lhs <= rhs,
            ArithOperator::Less => lhs < rhs,
            ArithOperator::Geq => lhs >= rhs,
            ArithOperator::Greater => lhs > rhs,
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
            ArithOperator::Eq => ArithOperator::Eq,
            ArithOperator::Ineq => ArithOperator::Ineq,
            ArithOperator::Leq => ArithOperator::Geq,
            ArithOperator::Less => ArithOperator::Greater,
            ArithOperator::Geq => ArithOperator::Leq,
            ArithOperator::Greater => ArithOperator::Less,
        }
    }
}

/// A linear constraint
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LinearConstraint {
    lhs: LinearArithTerm,
    rhs: i64,
    typ: ArithOperator,
    is_canonical: bool,
}

impl LinearConstraint {
    pub fn new(lhs: LinearArithTerm, typ: ArithOperator, rhs: i64) -> Self {
        Self {
            lhs,
            rhs,
            typ,
            is_canonical: false,
        }
    }

    pub fn lhs(&self) -> &LinearArithTerm {
        &self.lhs
    }
    pub fn rhs(&self) -> i64 {
        self.rhs
    }
    pub fn operator(&self) -> ArithOperator {
        self.typ
    }

    pub(crate) fn variables(&self) -> IndexSet<Rc<Variable>> {
        let mut vars = IndexSet::new();
        for f in self.lhs.iter() {
            match f {
                LinearSummand::Mult(x, _) => {
                    vars.insert(x.variable().clone());
                }
                LinearSummand::Const(_) => {}
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
            ArithOperator::Eq => ArithOperator::Ineq,
            ArithOperator::Ineq => ArithOperator::Eq,
            ArithOperator::Leq => ArithOperator::Greater,
            ArithOperator::Less => ArithOperator::Geq,
            ArithOperator::Geq => ArithOperator::Less,
            ArithOperator::Greater => ArithOperator::Leq,
        };
        let mut negated = LinearConstraint::new(self.lhs.clone(), new_op, self.rhs);
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
        let mut lhs_new = LinearArithTerm::new();
        for f in self.lhs.iter() {
            match f {
                LinearSummand::Mult(_, _) => lhs_new.add_summand(f.clone()),
                LinearSummand::Const(c) => rhs_new -= c,
            }
        }
        self.lhs = lhs_new;
        self.rhs = rhs_new;
        self.is_canonical = true;
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

impl Display for ArithOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArithOperator::Eq => write!(f, "="),
            ArithOperator::Ineq => write!(f, "!="),
            ArithOperator::Leq => write!(f, "<="),
            ArithOperator::Less => write!(f, "<"),
            ArithOperator::Geq => write!(f, ">="),
            ArithOperator::Greater => write!(f, ">"),
        }
    }
}

impl Display for LinearConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.typ, self.rhs)
    }
}

// TODO: Needs testing!

impl Arbitrary for ArithOperator {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        match u8::arbitrary(g) % 6 {
            0 => ArithOperator::Eq,
            1 => ArithOperator::Ineq,
            2 => ArithOperator::Leq,
            3 => ArithOperator::Less,
            4 => ArithOperator::Geq,
            5 => ArithOperator::Greater,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn test_operator_flip_flip(op: ArithOperator) -> bool {
        op.flip().flip() == op
    }
}
