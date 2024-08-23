use std::{collections::HashMap, fmt::Display, ops::Index};

use indexmap::IndexSet;

use crate::repr::{Sorted, Variable};

use super::ConstReducible;

/// Represents different types of variable-based terms in a linear expression.
/// This enum differentiates between a simple variable and the length of a string variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VariableTerm {
    Int(Variable), // A simple variable like x
    Len(Variable), // Represents |x|, the length of a string variable
}
impl VariableTerm {
    pub fn is_len(&self) -> bool {
        matches!(self, VariableTerm::Len(_))
    }

    pub fn is_int(&self) -> bool {
        matches!(self, VariableTerm::Int(_))
    }

    pub fn variable(&self) -> &Variable {
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
    Mult(VariableTerm, isize),
    /// A constant
    Const(isize),
}

impl LinearSummand {
    pub fn is_constant(&self) -> bool {
        match self {
            LinearSummand::Const(_) | LinearSummand::Mult(_, 0) => true, // 0*x = 0
            LinearSummand::Mult(_, _) => false,
        }
    }

    pub fn multiply(&self, c: isize) -> Self {
        match self {
            LinearSummand::Mult(x, c2) => LinearSummand::Mult(x.clone(), c * c2),
            LinearSummand::Const(c2) => LinearSummand::Const(c * c2),
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
}

impl LinearArithTerm {
    pub fn new() -> Self {
        Self { factors: vec![] }
    }

    /// Create a linear arithmetic term from a (int) variable
    /// Panics if the variable is not of sort int
    pub fn from_var(x: &Variable) -> Self {
        assert!(x.sort().is_int(), "Variable must be of sort int");
        Self {
            factors: vec![LinearSummand::Mult(VariableTerm::Int(x.clone()), 1)],
        }
    }

    /// Create a linear arithmetic term from the length of a string variable
    /// Panics if the variable is not of sort string
    pub fn from_var_len(x: &Variable) -> Self {
        assert!(x.sort().is_string(), "Variable must be of sort string");
        Self {
            factors: vec![LinearSummand::Mult(VariableTerm::Len(x.clone()), 1)],
        }
    }

    pub fn remove_factor(&mut self, f: &LinearSummand) -> bool {
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
            factors: vec![LinearSummand::Const(c)],
        }
    }

    pub fn add_summand(&mut self, f: LinearSummand) {
        self.factors.push(f);
    }

    pub fn extend(&mut self, other: Self) {
        self.factors.extend(other.factors);
    }

    pub fn iter(&self) -> impl Iterator<Item = &LinearSummand> {
        self.factors.iter()
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

    /// Normalize the term by combining all coefficients of the same variable.
    /// After calling this, there is at most one factor per variable and at most one constant.
    pub fn normalize(&mut self) {
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
            self.factors.push(LinearSummand::Mult(x, c));
        }
        if residual != 0 {
            self.factors.push(LinearSummand::Const(residual));
        }
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
    pub fn as_constant(&self) -> Option<isize> {
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
}

impl Index<usize> for LinearArithTerm {
    type Output = LinearSummand;

    fn index(&self, index: usize) -> &Self::Output {
        &self.factors[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LinearOperator {
    Eq,
    Ineq,
    Leq,
    Less,
    Geq,
    Greater,
}
impl LinearOperator {
    pub fn eval(&self, lhs: isize, rhs: isize) -> bool {
        match self {
            LinearOperator::Eq => lhs == rhs,
            LinearOperator::Ineq => lhs != rhs,
            LinearOperator::Leq => lhs <= rhs,
            LinearOperator::Less => lhs < rhs,
            LinearOperator::Geq => lhs >= rhs,
            LinearOperator::Greater => lhs > rhs,
        }
    }
}

/// A linear constraint
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LinearConstraint {
    pub lhs: LinearArithTerm,
    pub rhs: isize,
    pub typ: LinearOperator,
}

impl LinearConstraint {
    pub fn new(lhs: LinearArithTerm, typ: LinearOperator, rhs: isize) -> Self {
        Self { lhs, rhs, typ }
    }

    pub fn lhs(&self) -> &LinearArithTerm {
        &self.lhs
    }
    pub fn rhs(&self) -> isize {
        self.rhs
    }
    pub fn typ(&self) -> LinearOperator {
        self.typ
    }

    pub(crate) fn variables(&self) -> IndexSet<Variable> {
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
}

impl ConstReducible for LinearConstraint {
    fn is_constant(&self) -> Option<bool> {
        let lhs = self.lhs.as_constant()?;
        Some(self.typ().eval(lhs, self.rhs))
    }
}

//     /// Derive a linear constraint from a word equation
//     pub fn from_word_equation(eq: &WordEquation) -> Self {
//         let mut lhs = LinearArithTerm::new();
//         let mut rhs = 0;
//         for x in eq.variables() {
//             let xs = &Symbol::Variable(x.clone());
//             let coeff = eq.lhs().count(xs) as isize - eq.rhs().count(xs) as isize;
//             lhs.add_var_coeff(&x.len_var().unwrap(), coeff);
//         }
//         for c in eq.alphabet() {
//             let c = &Symbol::Constant(c);
//             let diff = eq.rhs().count(c) as isize - eq.lhs().count(c) as isize;
//             rhs += diff;
//         }

//         Self {
//             lhs,
//             rhs,
//             typ: LinearOperator::Eq,
//         }
//     }

//     /// Derive a linear constraint that restricts the upper bound for the patter from a regular constraint, if the regular language is finite.
//     /// The constraint is of the form `lhs <= rhs`, where `lhs` is the length of the pattern (i.e., the sum of the lenght all variable occurrences plus the length of the constant symbols) and `rhs` is the number of states in the automaton.
//     /// Note that there cannot be a word in the (finite) language that is longer than the number of states.
//     /// If the regular language is not finite, `None` is returned.
//     pub fn from_regular_constraint_upper(re: &RegularConstraint) -> Option<Self> {
//         if let Some(automaton) = re.get_automaton() {
//             if !automaton.acyclic() {
//                 return None;
//             }

//             let mut lhs = LinearArithTerm::new();
//             let mut rhs = 0;

//             for x in re.get_pattern().iter() {
//                 match x {
//                     Symbol::Constant(_) => rhs -= 1,
//                     Symbol::Variable(v) => {
//                         lhs.add_var_coeff(&v.len_var().unwrap(), 1);
//                     }
//                 }
//             }

//             rhs += re.get_automaton().unwrap().states().len() as isize;

//             Some(Self {
//                 lhs,
//                 rhs,
//                 typ: LinearOperator::Leq,
//             })
//         } else {
//             None
//         }
//     }

//     /// Derive a linear constraint that restricts the lower bound for the pattern from a regular constraint.
//     /// The constraint is of the form `lhs >= rhs`, where `lhs` is the length of the pattern (i.e., the sum of the lenght all variable occurrences plus the length of the constant symbols) and `rhs` is the shortest path from the initial state to a final state in the automaton.
//     pub fn from_regular_constraint_lower(re: &RegularConstraint) -> Self {
//         let automaton = re.get_automaton().unwrap();
//         let mut lhs = LinearArithTerm::new();
//         let mut rhs = 0;

//         for x in re.get_pattern().iter() {
//             match x {
//                 Symbol::Constant(_) => rhs -= 1,
//                 Symbol::Variable(v) => {
//                     lhs.add_var_coeff(&v.len_var().unwrap(), 1);
//                 }
//             }
//         }

//         rhs += automaton.shortest().unwrap_or(0) as isize;

//         Self {
//             lhs,
//             rhs,
//             typ: LinearOperator::Geq,
//         }
//     }
// }

// impl From<(LinearArithTerm, LinearArithTerm, LinearOperator)> for LinearConstraint {
//     fn from(value: (LinearArithTerm, LinearArithTerm, LinearOperator)) -> Self {
//         let lhs = value.0;
//         let rhs = value.1;
//         let typ = value.2;
//         if let Some(mut c) = rhs.is_constant() {
//             let mut lhs = lhs;
//             lhs.normalize();
//             let mut consts = vec![];
//             for fac in lhs.iter() {
//                 match fac {
//                     Summand::VarCoeff(_, _) => {}
//                     Summand::Const(c2) => {
//                         consts.push(fac.clone());
//                         c -= c2;
//                     }
//                 }
//             }
//             for fac in consts {
//                 lhs.remove_factor(&fac);
//             }
//             Self { lhs, rhs: c, typ }
//         } else {
//             let mut lhs = lhs.subtract(&rhs);
//             lhs.normalize();
//             let mut consts = vec![];
//             let mut c = 0;
//             for fac in lhs.iter() {
//                 match fac {
//                     Summand::VarCoeff(_, _) => {}
//                     Summand::Const(c2) => {
//                         consts.push(fac.clone());
//                         c -= c2;
//                     }
//                 }
//             }
//             for fac in consts {
//                 lhs.remove_factor(&fac);
//             }

//             Self { lhs, rhs: c, typ }
//         }
//     }
// }

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

impl Display for LinearOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinearOperator::Eq => write!(f, "="),
            LinearOperator::Ineq => write!(f, "!="),
            LinearOperator::Leq => write!(f, "<="),
            LinearOperator::Less => write!(f, "<"),
            LinearOperator::Geq => write!(f, ">="),
            LinearOperator::Greater => write!(f, ">"),
        }
    }
}

impl Display for LinearConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.lhs, self.typ, self.rhs)
    }
}

// TODO: Needs testing!
