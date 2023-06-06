use crate::model::words::Symbol;

use super::{words::WordEquation, Variable};

pub enum LinearType {
    Eq,
    Leq,
}

/// A linear constraint
pub struct LinearConstraint {
    pub lhs: Vec<(Variable, isize)>,
    pub rhs: isize,
    pub typ: LinearType,
}

impl LinearConstraint {
    /// Derive a linear constraint from a word equation
    pub fn from_word_equation(eq: &WordEquation) -> Self {
        let mut lhs = vec![];
        let mut rhs = 0;
        for x in eq.variables() {
            let xs = &Symbol::Variable(x.clone());
            let coeff = eq.lhs().count(xs) as isize - eq.rhs().count(xs) as isize;
            lhs.push((x.len_var(), coeff));
        }
        for c in eq.alphabet() {
            let c = &Symbol::Constant(c);
            let diff = eq.rhs().count(c) as isize - eq.lhs().count(c) as isize;
            rhs += diff as isize;
        }

        Self {
            lhs,
            rhs: rhs,
            typ: LinearType::Eq,
        }
    }
}
