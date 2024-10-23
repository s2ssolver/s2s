//! Conversion from IR to SMT-LIB2 format.

use crate::context::{Sorted, Variable};

use super::{
    Atom, AtomType, Contains, Formula, LinearArithTerm, LinearConstraint, LinearOperator, Literal,
    Pattern, PrefixOf, RegularConstraint, SuffixOf, Symbol, VariableTerm, WordEquation,
};

pub fn to_smtlib(fm: &Formula) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic QF_SLIA)\n");

    let vars = fm.variables();

    for var in vars {
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            var.to_smtlib(),
            var.sort()
        ));
    }

    let asserts = split_and_asserts(fm);
    for assert in asserts {
        smt.push_str(&format!("(assert {})\n", assert.to_smtlib()));
    }

    smt.push_str("(check-sat)\n");
    smt.push_str("(exit)\n");

    smt
}

/// Conversion to SMT-LIB format.
trait ToSmtLib {
    fn to_smtlib(&self) -> String;
}

fn split_and_asserts(fm: &Formula) -> Vec<&Formula> {
    match fm {
        Formula::And(fs) => fs.iter().flat_map(split_and_asserts).collect(),
        _ => vec![fm],
    }
}

impl ToSmtLib for Formula {
    fn to_smtlib(&self) -> String {
        match self {
            Formula::True => todo!(),
            Formula::False => todo!(),
            Formula::Literal(literal) => literal.to_smtlib(),
            Formula::And(vec) => format!(
                "(and {})",
                vec.iter()
                    .map(|f| f.to_smtlib())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Formula::Or(vec) => format!(
                "(or {})",
                vec.iter()
                    .map(|f| f.to_smtlib())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

impl ToSmtLib for Literal {
    fn to_smtlib(&self) -> String {
        let atom_smt = self.atom().to_smtlib();
        if self.polarity() {
            atom_smt
        } else {
            format!("(not {})", atom_smt)
        }
    }
}

impl ToSmtLib for Atom {
    fn to_smtlib(&self) -> String {
        self.get_type().to_smtlib()
    }
}

impl ToSmtLib for AtomType {
    fn to_smtlib(&self) -> String {
        match self {
            AtomType::BoolVar(v) => v.as_ref().to_smtlib(),
            AtomType::InRe(rc) => rc.to_smtlib(),
            AtomType::WordEquation(weq) => weq.to_smtlib(),
            AtomType::PrefixOf(po) => po.to_smtlib(),
            AtomType::SuffixOf(so) => so.to_smtlib(),
            AtomType::Contains(ct) => ct.to_smtlib(),
            AtomType::LinearConstraint(lc) => lc.to_smtlib(),
        }
    }
}

impl ToSmtLib for RegularConstraint {
    fn to_smtlib(&self) -> String {
        let pattern = self.pattern().to_smtlib();
        let re = regulaer::parse::to_smt(self.re());
        format!("(str.in_re {} {})", pattern, re)
    }
}

impl ToSmtLib for WordEquation {
    fn to_smtlib(&self) -> String {
        format!("(= {} {})", self.lhs().to_smtlib(), self.rhs().to_smtlib())
    }
}

impl ToSmtLib for PrefixOf {
    fn to_smtlib(&self) -> String {
        format!(
            "(str.prefixof {} {})",
            self.prefix().to_smtlib(),
            self.of().to_smtlib()
        )
    }
}

impl ToSmtLib for SuffixOf {
    fn to_smtlib(&self) -> String {
        format!(
            "(str.suffixof {} {})",
            self.suffix().to_smtlib(),
            self.of().to_smtlib()
        )
    }
}

impl ToSmtLib for Contains {
    fn to_smtlib(&self) -> String {
        format!(
            "(str.contains {} {})",
            self.haystack().to_smtlib(),
            self.needle().to_smtlib()
        )
    }
}

impl ToSmtLib for Pattern {
    fn to_smtlib(&self) -> String {
        let mut constw = String::new();
        let mut parts = vec![];
        for s in self.iter() {
            match s {
                Symbol::Constant(c) => constw.push(*c),
                Symbol::Variable(variable) => {
                    if !constw.is_empty() {
                        parts.push(format!("\"{}\"", constw));
                        constw.clear();
                    }
                    parts.push(variable.to_smtlib());
                }
            }
        }
        if !constw.is_empty() {
            parts.push(format!("\"{}\"", constw));
        }
        match parts.len() {
            0 => return "\"\"".to_string(),
            1 => parts[0].clone(),
            _ => format!("(str.++ {})", parts.join(" ")),
        }
    }
}

fn printable(v: &str) -> bool {
    v.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

impl ToSmtLib for Variable {
    fn to_smtlib(&self) -> String {
        if printable(self.name()) {
            self.name().to_string()
        } else {
            format!("|{}|", self.name())
        }
    }
}

impl ToSmtLib for LinearConstraint {
    fn to_smtlib(&self) -> String {
        let lhs = self.lhs().to_smtlib();
        let op = match self.operator() {
            super::LinearOperator::Eq | super::LinearOperator::Ineq => "=",
            super::LinearOperator::Leq => "<=",
            super::LinearOperator::Less => "<",
            super::LinearOperator::Geq => ">=",
            super::LinearOperator::Greater => ">",
        };
        let smt = format!("({} {} {})", op, lhs, self.rhs().to_smtlib());
        if self.operator() == LinearOperator::Ineq {
            format!("(not {})", smt)
        } else {
            smt
        }
    }
}

impl ToSmtLib for LinearArithTerm {
    fn to_smtlib(&self) -> String {
        let mut parts = vec![];
        for summand in self.iter() {
            match summand {
                super::LinearSummand::Mult(v, x) => {
                    parts.push(format!("(* {} {})", v.to_smtlib(), x.to_smtlib()))
                }
                super::LinearSummand::Const(c) => parts.push(c.to_smtlib()),
            }
        }
        match parts.len() {
            0 => "0".to_string(),
            1 => parts[0].clone(),
            _ => format!("(+ {})", parts.join(" ")),
        }
    }
}

impl ToSmtLib for VariableTerm {
    fn to_smtlib(&self) -> String {
        match self {
            VariableTerm::Int(variable) => variable.to_smtlib(),
            VariableTerm::Len(variable) => format!("(str.len {})", variable.to_smtlib()),
        }
    }
}

impl ToSmtLib for isize {
    fn to_smtlib(&self) -> String {
        if *self >= 0 {
            self.to_string()
        } else {
            format!("(- {})", self.abs())
        }
    }
}
