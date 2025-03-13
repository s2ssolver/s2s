//! An assignment is a mapping from variables to constant values.

use std::{fmt::Display, rc::Rc};

use indexmap::IndexMap;

use crate::node::{Node, NodeKind, NodeSubstitution, Sort, Sorted, Variable};

use super::{
    ArithOperator, Atom, AtomKind, FactorConstraintType, LinearArithTerm, LinearConstraint,
    LinearSummand, Literal, Pattern, RegularConstraint, RegularFactorConstraint, Symbol,
    VariableTerm, WordEquation,
};

/// The value of a variable in an assignment.
/// Based on the sort of the variable, the value can be a string, an integer, or a boolean.
#[derive(Debug, Clone)]
pub enum AssignedValue {
    String(String),
    Int(i64),
    Bool(bool),
}

impl AssignedValue {
    pub fn as_string(&self) -> Option<&String> {
        match self {
            Self::String(value) => Some(value),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
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
        Self::Int(value as i64)
    }
}

impl From<i64> for AssignedValue {
    fn from(value: i64) -> Self {
        Self::Int(value)
    }
}

impl From<u32> for AssignedValue {
    fn from(value: u32) -> Self {
        Self::Int(value as i64)
    }
}

impl From<bool> for AssignedValue {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<AssignedValue> for String {
    fn from(val: AssignedValue) -> Self {
        val.as_string().expect("Value is not a string").clone()
    }
}

impl From<AssignedValue> for isize {
    fn from(val: AssignedValue) -> Self {
        val.as_int().expect("Value is not an integer") as isize
    }
}

impl From<AssignedValue> for i32 {
    fn from(val: AssignedValue) -> Self {
        val.as_int().expect("Value is not an integer") as i32
    }
}

impl From<AssignedValue> for i64 {
    fn from(val: AssignedValue) -> Self {
        val.as_int().expect("Value is not an integer")
    }
}

impl From<AssignedValue> for bool {
    fn from(val: AssignedValue) -> Self {
        val.as_bool().expect("Value is not a boolean")
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
    pub fn get_int(&self, variable: &Variable) -> Option<i64> {
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

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<Variable>, &AssignedValue)> {
        self.values.iter()
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
    /// The formula is expected to be in canonical form.
    /// If it is not or if the formula contains unsupported constructs, the result is always false.
    pub fn satisfies(&self, formula: &Node) -> bool {
        match formula.kind() {
            NodeKind::And => formula.children().iter().all(|f| self.satisfies(f)),
            NodeKind::Or => formula.children().iter().any(|f| self.satisfies(f)),
            NodeKind::Literal(lit) => self.satisfies_lit(lit),
            NodeKind::Bool(t) => *t,
            NodeKind::Variable(v) if v.sort().is_bool() => {
                self.get_bool(v.as_ref()).map_or(false, |value| value)
            }
            NodeKind::Imp => {
                let lhs = self.satisfies(&formula.children()[0]);
                let rhs = self.satisfies(&formula.children()[1]);
                !lhs || rhs
            }
            NodeKind::Equiv => {
                let lhs = self.satisfies(&formula.children()[0]);
                let rhs = self.satisfies(&formula.children()[1]);
                lhs == rhs
            }
            NodeKind::Not => !self.satisfies(&formula.children()[0]),
            NodeKind::Ite => {
                let cond = self.satisfies(&formula.children()[0]);
                if cond {
                    self.satisfies(&formula.children()[1])
                } else {
                    self.satisfies(&formula.children()[2])
                }
            }
            NodeKind::Eq => {
                let lhs = &formula.children()[0];
                let rhs = &formula.children()[1];
                match (lhs.sort(), rhs.sort()) {
                    (Sort::String, Sort::String) => {
                        let lhs = self.inst_string_term(lhs);
                        let rhs = self.inst_string_term(rhs);
                        match (lhs, rhs) {
                            (Some(lhs), Some(rhs)) => lhs == rhs,
                            _ => false,
                        }
                    }
                    (Sort::Int, Sort::Int) => {
                        let lhs = self.inst_int_term(lhs);
                        let rhs = self.inst_int_term(rhs);
                        match (lhs, rhs) {
                            (Some(lhs), Some(rhs)) => lhs == rhs,
                            _ => false,
                        }
                    }
                    _ => unreachable!("Unexpected formula: {}", formula),
                }
            }
            NodeKind::PrefixOf => {
                let lhs = self.inst_string_term(&formula.children()[0]);
                let rhs = self.inst_string_term(&formula.children()[1]);

                match (lhs, rhs) {
                    (Some(prefix), Some(of)) => of.starts_with(&prefix),
                    _ => false,
                }
            }
            NodeKind::SuffixOf => {
                let suffix = self.inst_string_term(&formula.children()[0]);
                let of = self.inst_string_term(&formula.children()[1]);
                match (suffix, of) {
                    (Some(suffix), Some(of)) => of.ends_with(&suffix),
                    _ => false,
                }
            }
            NodeKind::Contains => {
                let hay = self.inst_string_term(&formula.children()[0]);
                let needle = self.inst_string_term(&formula.children()[1]);
                match (hay, needle) {
                    (Some(hay), Some(needle)) => hay.contains(&needle),
                    _ => false,
                }
            }
            NodeKind::InRe => {
                let lhs = self.inst_string_term(&formula.children()[0]);
                if let NodeKind::Regex(re) = &formula.children()[1].kind() {
                    re.accepts(&lhs.unwrap().into())
                } else {
                    panic!("Unexpected formula: {}", formula)
                }
            }
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => {
                let lhs = self.inst_int_term(&formula.children()[0]);
                let rhs = self.inst_int_term(&formula.children()[1]);
                match (lhs, rhs) {
                    (Some(lhs), Some(rhs)) => match formula.kind() {
                        NodeKind::Lt => lhs < rhs,
                        NodeKind::Le => lhs <= rhs,
                        NodeKind::Gt => lhs > rhs,
                        NodeKind::Ge => lhs >= rhs,
                        _ => unreachable!(),
                    },
                    _ => false,
                }
            }

            _ => unreachable!("Unexpected formula: {}", formula),
        }
    }

    fn inst_string_term(&self, term: &Node) -> Option<String> {
        match term.kind() {
            NodeKind::String(s) => Some(s.clone()),
            NodeKind::Variable(v) => self.get_str(v.as_ref()).cloned(),
            NodeKind::Concat => {
                let mut result = String::new();
                for child in term.children() {
                    result.push_str(&self.inst_string_term(child)?);
                }
                Some(result)
            }
            NodeKind::Replace => {
                let mut result = self.inst_string_term(&term.children()[0])?;
                let from = self.inst_string_term(&term.children()[1])?;
                let to = self.inst_string_term(&term.children()[2])?;
                result = result.replacen(&from, &to, 1);
                Some(result)
            }
            NodeKind::ReplaceAll => {
                let mut result = self.inst_string_term(&term.children()[0])?;
                let from = self.inst_string_term(&term.children()[1])?;
                let to = self.inst_string_term(&term.children()[2])?;
                result = result.replace(&from, &to);
                Some(result)
            }
            NodeKind::SubStr | NodeKind::At => {
                todo!()
            }
            _ => None,
        }
    }

    fn inst_int_term(&self, term: &Node) -> Option<i64> {
        match term.kind() {
            NodeKind::Int(i) => Some(*i),
            NodeKind::Variable(v) => self.get_int(v.as_ref()),
            NodeKind::Add => {
                let mut result = 0;
                for child in term.children() {
                    result += self.inst_int_term(child)?;
                }
                Some(result)
            }
            NodeKind::Sub => {
                let mut result = self.inst_int_term(&term.children()[0])?;
                for child in term.children().iter().skip(1) {
                    result -= self.inst_int_term(child)?;
                }
                Some(result)
            }
            NodeKind::Mul => {
                let mut result = 1;
                for child in term.children() {
                    result *= self.inst_int_term(child)?;
                }
                Some(result)
            }
            NodeKind::Neg => {
                let child = &term.children()[0];
                Some(-self.inst_int_term(child)?)
            }
            _ => None,
        }
    }

    pub fn satisfies_lit(&self, literal: &Literal) -> bool {
        let s_atom = self.satisfies_atom(literal.atom());
        s_atom == literal.polarity()
    }

    pub fn satisfies_atom(&self, atom: &Atom) -> bool {
        match atom.kind() {
            AtomKind::Boolvar(v) => self.get_bool(v.as_ref()).map_or(false, |value| value),
            AtomKind::WordEquation(we) => self.satisfies_word_equation(we),
            AtomKind::InRe(inre) => self.satisfies_inre(inre),
            AtomKind::FactorConstraint(fc) => self.satisfies_factor_constraint(fc),
            AtomKind::Linear(lc) => self.satisfies_arith_constraint(lc),
        }
    }

    pub fn satisfies_word_equation(&self, eq: &WordEquation) -> bool {
        match eq {
            WordEquation::ConstantEquality(l, r) => l == r,
            WordEquation::VarEquality(l, r) => {
                match (self.get_str(l.as_ref()), self.get_str(r.as_ref())) {
                    (Some(l), Some(r)) => l == r,
                    _ => false,
                }
            }
            WordEquation::VarAssignment(l, r) => match self.get_str(l.as_ref()) {
                Some(value) => value == r,
                None => false,
            },
            WordEquation::General(l, r) => match (self.apply_pattern(l), self.apply_pattern(r)) {
                (Some(l), Some(r)) => l == r,
                _ => false,
            },
        }
    }

    pub fn satisfies_inre(&self, inre: &RegularConstraint) -> bool {
        if let Some(value) = self.get_str(inre.lhs().as_ref()) {
            inre.re().accepts(&value.clone().into())
        } else {
            false
        }
    }

    pub fn satisfies_factor_constraint(&self, fc: &RegularFactorConstraint) -> bool {
        if let Some(value) = self.get_str(fc.of().as_ref()) {
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

    pub fn satisfies_arith_constraint(&self, lc: &LinearConstraint) -> bool {
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

    fn apply_pattern(&self, pattern: &Pattern) -> Option<String> {
        let mut result = String::new();
        for sym in pattern.symbols() {
            match sym {
                Symbol::Constant(c) => result.push(*c),
                Symbol::Variable(rc) => result.push_str(self.get_str(rc.as_ref())?),
            }
        }
        Some(result)
    }

    fn apply_arith_term(&self, term: &LinearArithTerm) -> Option<i64> {
        let mut res = 0;
        for summand in term.iter() {
            match summand {
                LinearSummand::Mult(v, s) => {
                    let value = match v {
                        VariableTerm::Int(vv) => self.get_int(vv.as_ref()),
                        VariableTerm::Len(vv) => {
                            self.get_str(vv.as_ref()).map(|s| s.chars().count() as i64)
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

impl From<NodeSubstitution> for Assignment {
    fn from(subs: NodeSubstitution) -> Self {
        let mut assignment = Assignment::new();
        for (lhs, rhs) in subs.iter() {
            let value = match rhs.kind() {
                NodeKind::Bool(b) => AssignedValue::Bool(*b),
                NodeKind::String(s) => AssignedValue::String(s.clone()),
                NodeKind::Int(i) => AssignedValue::Int(*i),
                _ => continue,
            };
            assignment.assign(lhs.clone(), value.clone());
        }
        assignment
    }
}

impl Display for AssignedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(value) => write!(f, "{}", value),
            Self::Int(value) => write!(f, "{}", value),
            Self::Bool(value) => write!(f, "{}", value),
        }
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (variable, value) in self.values.iter() {
            writeln!(f, "{} -> {}", variable, value)?;
        }
        Ok(())
    }
}
