use std::collections::HashMap;

use crate::{
    context::Context,
    repr::{
        ir::{AtomType, Formula, LinearArithTerm, Literal, Pattern, Symbol, WordEquation},
        Variable,
    },
};

use super::LiteralSimplifier;

/// We call a regular constraint independent if it has the form `x \in R` where `x` is a variable and `R` is a regular expression and `x` does not occur elsewhere in the formula.
pub struct IndependetVarConstraint {
    var_count: HashMap<Variable, usize>,
}

impl IndependetVarConstraint {
    pub fn new() -> Self {
        Self {
            var_count: HashMap::new(),
        }
    }

    fn count_vars(&mut self, fm: &Formula) -> HashMap<Variable, usize> {
        match fm {
            Formula::Literal(l) => match l.atom().get_type() {
                AtomType::BoolVar(_) => todo!(),
                AtomType::InRe(inre) => Self::count_pattern_vars(inre.pattern()),
                AtomType::WordEquation(WordEquation::VarAssignment(x, _)) => {
                    let mut count = HashMap::new();
                    *count.entry(x.clone()).or_default() += 1;
                    count
                }
                AtomType::WordEquation(WordEquation::VarEquality(x, y)) => {
                    let mut count = HashMap::new();
                    *count.entry(x.clone()).or_default() += 1;
                    *count.entry(y.clone()).or_default() += 1;
                    count
                }
                AtomType::WordEquation(WordEquation::General(l, r)) => {
                    let l_count = Self::count_pattern_vars(l);
                    let r_count = Self::count_pattern_vars(r);
                    Self::add(l_count, r_count)
                }
                AtomType::PrefixOf(pr) => {
                    let l_count = Self::count_pattern_vars(pr.prefix());
                    let r_count = Self::count_pattern_vars(pr.of());
                    Self::add(l_count, r_count)
                }
                AtomType::SuffixOf(suf) => {
                    let l_count = Self::count_pattern_vars(suf.suffix());
                    let r_count = Self::count_pattern_vars(suf.of());
                    Self::add(l_count, r_count)
                }
                AtomType::Contains(ct) => {
                    let l_count = Self::count_pattern_vars(ct.needle());
                    let r_count = Self::count_pattern_vars(ct.haystack());
                    Self::add(l_count, r_count)
                }
                AtomType::LinearConstraint(l) => Self::count_linear_vars(l.lhs()),
                _ => HashMap::new(),
            },
            Formula::And(fs) | Formula::Or(fs) => {
                let mut count = HashMap::new();
                for f in fs {
                    let f_count = self.count_vars(f);
                    count = Self::add(count, f_count);
                }
                count
            }
            _ => HashMap::new(),
        }
    }

    fn add(c1: HashMap<Variable, usize>, c2: HashMap<Variable, usize>) -> HashMap<Variable, usize> {
        let mut count = c1;
        for (var, c) in c2 {
            *count.entry(var).or_default() += c;
        }
        count
    }

    fn count_pattern_vars(pat: &Pattern) -> HashMap<Variable, usize> {
        let mut count = HashMap::new();
        for var in pat.iter().filter_map(|s| {
            if let Symbol::Variable(v) = s {
                Some(v)
            } else {
                None
            }
        }) {
            *count.entry(var.clone()).or_default() += 1;
        }
        count
    }

    fn count_linear_vars(t: &LinearArithTerm) -> HashMap<Variable, usize> {
        let mut count = HashMap::new();
        for var in t.iter().filter_map(|s| match s {
            crate::repr::ir::LinearSummand::Mult(vt, _) => Some(vt.variable()),
            crate::repr::ir::LinearSummand::Const(_) => None,
        }) {
            *count.entry(var.clone()).or_default() += 1;
        }
        count
    }
}

impl LiteralSimplifier for IndependetVarConstraint {
    fn simplify(&self, lit: &Literal, ctx: &mut Context) -> super::SimplificationResult<Literal> {
        todo!("Reduce based on independent variable constraints")
    }
}
