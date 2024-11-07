//! An assignment is a mapping from variables to constant values.

use std::rc::Rc;

use indexmap::IndexMap;

use crate::context::Variable;

use super::{
    ArithOperator, Atom, AtomKind, FactorConstraintType, Formula, FormulaKind, LinearArithTerm,
    LinearSummand, Literal, Pattern, Symbol, VariableTerm, WordEquation,
};

/// The value of a variable in an assignment.
/// Based on the sort of the variable, the value can be a string, an integer, or a boolean.
#[derive(Debug, Clone)]
enum AssignedValue {
    String(String),
    Int(isize),
    Bool(bool),
}

impl AssignedValue {
    pub fn as_string(&self) -> Option<&String> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<isize> {
        match self {
            Self::Int(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }
}

impl From<String> for AssignedValue {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<i32> for AssignedValue {
    fn from(value: i32) -> Self {
        Self::Int(value as isize)
    }
}

impl From<isize> for AssignedValue {
    fn from(value: isize) -> Self {
        Self::Int(value)
    }
}

impl From<i64> for AssignedValue {
    fn from(value: i64) -> Self {
        Self::Int(value as isize)
    }
}

impl From<u32> for AssignedValue {
    fn from(value: u32) -> Self {
        Self::Int(value as isize)
    }
}

impl From<bool> for AssignedValue {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl Into<String> for AssignedValue {
    fn into(self) -> String {
        self.as_string().expect("Value is not a string").clone()
    }
}

impl Into<isize> for AssignedValue {
    fn into(self) -> isize {
        self.as_int().expect("Value is not an integer")
    }
}

impl Into<i32> for AssignedValue {
    fn into(self) -> i32 {
        self.as_int().expect("Value is not an integer") as i32
    }
}

impl Into<i64> for AssignedValue {
    fn into(self) -> i64 {
        self.as_int().expect("Value is not an integer") as i64
    }
}

impl Into<bool> for AssignedValue {
    fn into(self) -> bool {
        self.as_bool().expect("Value is not a boolean")
    }
}

#[derive(Debug, Clone, Default)]
pub struct Assignment {
    /// The mapping from variables to constant values.
    values: IndexMap<Rc<Variable>, AssignedValue>,
}

impl Assignment {
    /// Creates a new assignment.
    pub fn new() -> Self {
        Self {
            values: IndexMap::new(),
        }
    }

    /// Assigns a string value to a variable.
    /// Panics if the variable is not of sort string.
    /// Returns the previous value of the variable, if any.
    pub fn assign(
        &mut self,
        variable: Rc<Variable>,
        value: impl Into<AssignedValue>,
    ) -> Option<AssignedValue> {
        self.values.insert(variable, value.into())
    }

    pub fn get(&self, variable: &Variable) -> Option<&AssignedValue> {
        self.values.get(variable)
    }

    /// Returns the value of a variable in the assignment.
    pub fn get_str(&self, variable: &Variable) -> Option<&String> {
        self.values.get(variable).and_then(|value| match value {
            AssignedValue::String(value) => Some(value),
            _ => None,
        })
    }

    /// Returns the value of a variable in the assignment.
    pub fn get_int(&self, variable: &Variable) -> Option<isize> {
        self.values.get(variable).and_then(|value| match value {
            AssignedValue::Int(value) => Some(*value),
            _ => None,
        })
    }

    /// Returns the value of a variable in the assignment.
    pub fn get_bool(&self, variable: &Variable) -> Option<bool> {
        self.values.get(variable).and_then(|value| match value {
            AssignedValue::Bool(value) => Some(*value),
            _ => None,
        })
    }

    /// Extends the assignment with the values from another assignment.
    /// If a variable is already assigned in the current assignment, the value is overwritten.
    /// Returns the number of variables that were overwritten.
    pub fn extend(&mut self, other: &Self) -> usize {
        let mut overwrites = 0;
        for (variable, value) in other.values.iter() {
            if self.values.contains_key(variable) {
                overwrites += 1;
            }
            self.values.insert(variable.clone(), value.clone());
        }
        overwrites
    }

    /// Checks if the assignment satisfies a formula.
    /// Returns true if the assignment satisfies the formula, false otherwise.
    /// Specifically, returns false if the truth value of the formula can not be evaluated in case the assignment is partial.
    /// Formulas of type `Unsupported` are always considered to be false.
    pub fn satisfies(&self, formula: &Formula) -> bool {
        match formula.kind() {
            FormulaKind::And(fs) => fs.iter().all(|f| self.satisfies(f)),
            FormulaKind::Or(fs) => fs.iter().any(|f| self.satisfies(f)),
            FormulaKind::Literal(lit) => self.satisfies_lit(lit),
            FormulaKind::Unsupported(_) => false,
        }
    }

    pub fn satisfies_lit(&self, literal: &Literal) -> bool {
        let s_atom = self.satisfies_atom(literal.atom());
        s_atom == literal.polarity()
    }

    pub fn satisfies_atom(&self, atom: &Atom) -> bool {
        match atom.kind() {
            AtomKind::Boolvar(v) => self.get_bool(&v).map_or(false, |value| value),
            AtomKind::WordEquation(WordEquation::ConstantEquality(_, _)) => true,
            AtomKind::WordEquation(WordEquation::VarEquality(l, r)) => {
                match (self.get_str(&l), self.get_str(&r)) {
                    (Some(l), Some(r)) => l == r,
                    _ => false,
                }
            }
            AtomKind::WordEquation(WordEquation::VarAssignment(l, r)) => match self.get_str(&l) {
                Some(value) => value == r,
                None => false,
            },
            AtomKind::WordEquation(WordEquation::General(l, r)) => {
                match (self.apply_pattern(&l), self.apply_pattern(&r)) {
                    (Some(l), Some(r)) => l == r,
                    _ => false,
                }
            }
            AtomKind::InRe(inre) => {
                if let Some(value) = self.get_str(&inre.lhs()) {
                    inre.re().accepts(&value.clone().into())
                } else {
                    false
                }
            }
            AtomKind::FactorConstraint(fc) => {
                if let Some(value) = self.get_str(fc.lhs()) {
                    let rhs = fc.rhs();
                    match fc.typ() {
                        FactorConstraintType::Prefix => value.starts_with(rhs),
                        FactorConstraintType::Suffix => value.ends_with(rhs),
                        FactorConstraintType::Contains => value.contains(rhs),
                    }
                } else {
                    false
                }
            }
            AtomKind::Linear(lc) => {
                let lhs_value = self.apply_arith_term(lc.lhs());
                if let Some(lhs_value) = lhs_value {
                    match lc.operator() {
                        ArithOperator::Eq => lhs_value == lc.rhs(),
                        ArithOperator::Ineq => lhs_value != lc.rhs(),
                        ArithOperator::Leq => lhs_value <= lc.rhs(),
                        ArithOperator::Less => lhs_value < lc.rhs(),
                        ArithOperator::Geq => lhs_value >= lc.rhs(),
                        ArithOperator::Greater => lhs_value > lc.rhs(),
                    }
                } else {
                    false
                }
            }
        }
    }

    fn apply_pattern(&self, pattern: &Pattern) -> Option<String> {
        let mut result = String::new();
        for sym in pattern.symbols() {
            match sym {
                Symbol::Constant(c) => result.push(*c),
                Symbol::Variable(rc) => result.push_str(self.get_str(rc)?),
            }
        }
        Some(result)
    }

    fn apply_arith_term(&self, term: &LinearArithTerm) -> Option<isize> {
        let mut res = 0;
        for summand in term.iter() {
            match summand {
                LinearSummand::Mult(v, s) => {
                    let value = match v {
                        VariableTerm::Int(vv) => self.get_int(vv),
                        VariableTerm::Len(vv) => {
                            self.get_str(vv).map(|s| s.chars().count() as isize)
                        }
                    };
                    if let Some(value) = value {
                        res += value * s;
                    } else {
                        return None;
                    }
                }
                LinearSummand::Const(i) => res += i,
            }
        }
        Some(res)
    }
}
