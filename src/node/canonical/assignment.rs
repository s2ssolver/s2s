//! An assignment is a mapping from variables to constant values.

use std::{fmt::Display, rc::Rc};

use indexmap::IndexMap;
use smtlib_str::SmtString;

use crate::node::{Node, NodeKind, Sort, Sorted, VarSubstitution, Variable};

use super::{
    ArithOperator, Atom, AtomKind, FactorConstraintType, LinearArithTerm, LinearConstraint,
    LinearSummand, Literal, Pattern, RegularConstraint, RegularFactorConstraint, Symbol,
    VariableTerm, WordEquation,
};

/// The value of a variable in an assignment.
/// Based on the sort of the variable, the value can be a string, an integer, or a boolean.
#[derive(Debug, Clone)]
pub enum AssignedValue {
    String(SmtString),
    Int(i64),
    Bool(bool),
}

impl AssignedValue {
    pub fn as_string(&self) -> Option<&SmtString> {
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

impl From<SmtString> for AssignedValue {
    fn from(value: SmtString) -> Self {
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

impl From<AssignedValue> for SmtString {
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
    pub fn get_str(&self, variable: &Variable) -> Option<&SmtString> {
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
    pub fn satisfies(&self, formula: &Node) -> Option<bool> {
        match formula.kind() {
            NodeKind::And => {
                for c in formula.children() {
                    if !self.satisfies(c)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            NodeKind::Or => {
                let mut none = false;
                for c in formula.children() {
                    match self.satisfies(c) {
                        Some(true) => return Some(true),
                        Some(false) => (),
                        None => none = true,
                    }
                }
                if none {
                    None
                } else {
                    Some(false)
                }
            }
            NodeKind::Literal(lit) => self.satisfies_lit(lit),
            NodeKind::Bool(t) => Some(*t),
            NodeKind::Variable(v) if v.sort().is_bool() => self.get_bool(v.as_ref()),
            NodeKind::Imp => {
                let lhs = self.satisfies(&formula.children()[0])?;
                let rhs = self.satisfies(&formula.children()[1])?;
                Some(!lhs || rhs)
            }
            NodeKind::Equiv => {
                let lhs = self.satisfies(&formula.children()[0])?;
                let rhs = self.satisfies(&formula.children()[1])?;
                Some(lhs == rhs)
            }
            NodeKind::Not => Some(!self.satisfies(&formula.children()[0])?),
            NodeKind::Ite => {
                let cond = self.satisfies(&formula.children()[0])?;
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
                        let lhs = self.inst_string_term(lhs)?;
                        let rhs = self.inst_string_term(rhs)?;
                        Some(lhs == rhs)
                    }
                    (Sort::Int, Sort::Int) => {
                        let lhs = self.inst_int_term(lhs)?;
                        let rhs = self.inst_int_term(rhs)?;
                        Some(lhs == rhs)
                    }
                    _ => unreachable!("Unexpected formula: {}", formula),
                }
            }
            NodeKind::PrefixOf => {
                let prefix = self.inst_string_term(&formula.children()[0])?;
                let of = self.inst_string_term(&formula.children()[1])?;
                Some(of.starts_with(&prefix))
            }
            NodeKind::SuffixOf => {
                let suffix = self.inst_string_term(&formula.children()[0])?;
                let of = self.inst_string_term(&formula.children()[1])?;
                Some(of.ends_with(&suffix))
            }
            NodeKind::Contains => {
                let hay = self.inst_string_term(&formula.children()[0])?;
                let needle = self.inst_string_term(&formula.children()[1])?;
                Some(hay.contains(&needle))
            }
            NodeKind::InRe => {
                let lhs = self.inst_string_term(&formula.children()[0])?;
                if let NodeKind::Regex(re) = &formula.children()[1].kind() {
                    Some(re.accepts(&lhs))
                } else {
                    unreachable!("Unexpected formula: {}", formula)
                }
            }
            NodeKind::Lt | NodeKind::Le | NodeKind::Gt | NodeKind::Ge => {
                let lhs = self.inst_int_term(&formula.children()[0])?;
                let rhs = self.inst_int_term(&formula.children()[1])?;
                let r = match formula.kind() {
                    NodeKind::Lt => lhs < rhs,
                    NodeKind::Le => lhs <= rhs,
                    NodeKind::Gt => lhs > rhs,
                    NodeKind::Ge => lhs >= rhs,
                    _ => unreachable!(),
                };
                Some(r)
            }

            _ => unreachable!("Unexpected formula: {}", formula),
        }
    }

    fn inst_string_term(&self, term: &Node) -> Option<SmtString> {
        let t = match term.kind() {
            NodeKind::String(s) => Some(s.clone()),
            NodeKind::Variable(v) => self.get_str(v.as_ref()).cloned(),
            NodeKind::Concat => {
                let mut result = SmtString::empty();
                for child in term.children() {
                    result.append(&self.inst_string_term(child)?);
                }
                Some(result)
            }
            NodeKind::Replace => {
                let mut result = self.inst_string_term(&term.children()[0])?;
                let from = self.inst_string_term(&term.children()[1])?;
                let to = self.inst_string_term(&term.children()[2])?;
                result = result.replace(&from, &to);
                Some(result)
            }
            NodeKind::ReplaceAll => {
                let mut result = self.inst_string_term(&term.children()[0])?;
                let from = self.inst_string_term(&term.children()[1])?;
                let to = self.inst_string_term(&term.children()[2])?;
                result = result.replace_all(&from, &to);
                Some(result)
            }
            NodeKind::SubStr => {
                let s = self.inst_string_term(&term.children()[0])?;

                let start = self.inst_int_term(&term.children()[1])?;

                let len = self.inst_int_term(&term.children()[2])?;

                let substr = if 0 <= start && start <= s.len() as i64 && 0 <= len {
                    let start = start as usize;
                    let len = len as usize;
                    s.drop(start).take(len)
                } else {
                    SmtString::empty()
                };

                Some(substr)
            }
            NodeKind::At => {
                let s = self.inst_string_term(&term.children()[0])?;
                let i = self.inst_int_term(&term.children()[1])?;

                if i < 0 {
                    return Some(SmtString::empty());
                }
                let i = i as usize;

                match s.nth(i) {
                    Some(c) => Some(SmtString::from(c)),
                    None => Some(SmtString::empty()),
                }
            }
            NodeKind::FromInt => {
                let i = self.inst_int_term(&term.children()[0])?;
                if i < 0 {
                    return Some(SmtString::empty());
                } else {
                    Some(i.to_string().into()) // TODO: Double check if this is correct
                }
            }
            _ => None,
        };
        t
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
            NodeKind::Length => {
                let s = self.inst_string_term(&term.children()[0])?;
                Some(s.len() as i64)
            }
            NodeKind::ToInt => {
                let s = self.inst_string_term(&term.children()[0])?;
                // convet to positive int base 10, or -1 if not possible
                // todo: double check if the conversion is correct
                match s.to_string().parse::<u64>() {
                    Ok(i) => Some(i as i64),
                    Err(_) => Some(-1),
                }
            }
            _ => None,
        }
    }

    pub fn satisfies_lit(&self, literal: &Literal) -> Option<bool> {
        let s_atom = self.satisfies_atom(literal.atom())?;
        Some(s_atom == literal.polarity())
    }

    pub fn satisfies_atom(&self, atom: &Atom) -> Option<bool> {
        match atom.kind() {
            AtomKind::Boolvar(v) => self.get_bool(v.as_ref()),
            AtomKind::WordEquation(we) => self.satisfies_word_equation(we),
            AtomKind::InRe(inre) => self.satisfies_inre(inre),
            AtomKind::FactorConstraint(fc) => self.satisfies_factor_constraint(fc),
            AtomKind::Linear(lc) => self.satisfies_arith_constraint(lc),
        }
    }

    pub fn satisfies_word_equation(&self, eq: &WordEquation) -> Option<bool> {
        match eq {
            WordEquation::ConstantEquality(l, r) => Some(l == r),
            WordEquation::VarEquality(l, r) => {
                Some(self.get_str(l.as_ref())? == self.get_str(r.as_ref())?)
            }
            WordEquation::VarAssignment(l, r) => {
                let l = self.get_str(l.as_ref())?;
                Some(l == r)
            }
            WordEquation::General(l, r) => {
                let l = self.apply_pattern(l)?;
                let r = self.apply_pattern(r)?;
                Some(l == r)
            }
        }
    }

    pub fn satisfies_inre(&self, inre: &RegularConstraint) -> Option<bool> {
        let lhs = self.get_str(inre.lhs().as_ref())?.clone();
        Some(inre.re().accepts(&lhs))
    }

    pub fn satisfies_factor_constraint(&self, fc: &RegularFactorConstraint) -> Option<bool> {
        let value = self.get_str(fc.of().as_ref())?;
        let rhs = fc.rhs();
        let r = match fc.typ() {
            FactorConstraintType::Prefix => value.starts_with(rhs),
            FactorConstraintType::Suffix => value.ends_with(rhs),
            FactorConstraintType::Contains => value.contains(rhs),
        };
        Some(r)
    }

    pub fn satisfies_arith_constraint(&self, lc: &LinearConstraint) -> Option<bool> {
        let lhs_value = self.apply_arith_term(lc.lhs())?;

        let r = match lc.operator() {
            ArithOperator::Eq => lhs_value == lc.rhs(),
            ArithOperator::Ineq => lhs_value != lc.rhs(),
            ArithOperator::Leq => lhs_value <= lc.rhs(),
            ArithOperator::Less => lhs_value < lc.rhs(),
            ArithOperator::Geq => lhs_value >= lc.rhs(),
            ArithOperator::Greater => lhs_value > lc.rhs(),
        };
        Some(r)
    }

    fn apply_pattern(&self, pattern: &Pattern) -> Option<SmtString> {
        let mut result = SmtString::empty();
        for sym in pattern.symbols() {
            match sym {
                Symbol::Constant(c) => result.push(*c),
                Symbol::Variable(rc) => result.append(self.get_str(rc.as_ref())?),
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
                        VariableTerm::Len(vv) => self.get_str(vv.as_ref()).map(|s| s.len() as i64),
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

impl From<VarSubstitution> for Assignment {
    fn from(subs: VarSubstitution) -> Self {
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
