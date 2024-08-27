use indexmap::IndexMap;
use std::collections::HashMap;
use std::fmt::{Display, Write};

use crate::{
    context::Context,
    repr::{Sort, Sorted, Variable},
};

use super::{int::LinearSummand, string::Symbol, AtomType, Formula, LinearArithTerm, Pattern};
use super::{Literal, VariableTerm};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Substitute {
    String(Pattern),
    Int(LinearArithTerm),
    Bool(bool),
}

impl Substitute {
    pub fn is_constant(&self) -> bool {
        match self {
            Self::String(p) => p.is_constant(),
            Self::Int(t) => t.as_constant().is_some(),
            Self::Bool(_) => true,
        }
    }

    pub fn as_string(&self) -> &Pattern {
        match self {
            Self::String(p) => p,
            _ => panic!("Expected a string term"),
        }
    }

    pub fn as_int(&self) -> &LinearArithTerm {
        match self {
            Self::Int(t) => t,
            _ => panic!("Expected an integer term"),
        }
    }
}

impl Display for Substitute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(p) => write!(f, "{}", p),
            Self::Int(t) => write!(f, "{}", t),
            Self::Bool(fm) => write!(f, "{}", fm),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VarSubstitution {
    subs: IndexMap<Variable, Substitute>,
}

/// A substitution of [variables](Variable) by [Substitute]s.
/// A variable of sort [string](Sort::String) can be substituted by [Pattern], a variable of sort [int](Sort::Int) can be substituted by an [LinearArithTerm].
impl VarSubstitution {
    pub fn empty() -> Self {
        Self {
            subs: IndexMap::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.subs.is_empty()
    }

    /// Returns true if the substitution is an assignemt.
    /// We call a substitution an assignment if it substitutes variables with constants.
    pub fn is_assignment(&self) -> bool {
        for (_, val) in &self.subs {
            if !val.is_constant() {
                return false;
            }
        }
        true
    }

    pub fn get(&self, var: &Variable) -> Option<&Substitute> {
        self.subs.get(var)
    }

    pub fn set(&mut self, var: Variable, term: Substitute) -> Option<Substitute> {
        self.subs.insert(var.clone(), term.clone())
    }

    pub fn set_str(&mut self, var: Variable, pat: Pattern) -> Option<Substitute> {
        debug_assert!(var.sort() == Sort::String);
        self.set(var, Substitute::String(pat))
    }

    pub fn set_int(&mut self, var: Variable, term: LinearArithTerm) -> Option<Substitute> {
        debug_assert!(var.sort() == Sort::Int);
        self.set(var, Substitute::Int(term))
    }

    fn pattern_to_len(pat: &Pattern) -> LinearArithTerm {
        let mut vs = HashMap::new();
        let mut r = 0;
        for s in pat.iter() {
            match s {
                Symbol::Constant(_) => r += 1,
                Symbol::Variable(v) => {
                    *vs.entry(v.clone()).or_insert(0) += 1;
                }
            }
        }
        let mut term = LinearArithTerm::new();
        vs.into_iter().for_each(|(v, c)| {
            let len = VariableTerm::Len(v);
            term.add_summand(LinearSummand::Mult(len, c));
        });
        term.add_summand(LinearSummand::Const(r));

        term
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Substitute)> {
        self.subs.iter()
    }

    /// Calculates the composition of two substitutions.
    /// The result is the substitution that results from applying the given substitution to this substitution.
    /// If the given substitution defines variables that are not defined in this substitution, the result will contain these variables.
    pub fn compose(&self, other: &Self) -> Self {
        let mut sub = Self::empty();
        for (var, val) in &self.subs {
            let chained = match val {
                Substitute::String(p) => {
                    let new_p = other.apply_pattern(&p);
                    Substitute::String(new_p)
                }
                Substitute::Int(t) => {
                    let new_t = other.apply_arith_term(&t);
                    Substitute::Int(new_t)
                }
                Substitute::Bool(b) => Substitute::Bool(*b),
            };
            sub.set(var.clone(), chained);
        }
        for (var, val) in &other.subs {
            // Add the substitution if it is not yet present
            if sub.get(var).is_none() {
                sub.set(var.clone(), val.clone());
            }
        }
        sub
    }

    /// Returns the SMT-LIB representation of this substitution if is an assignment.
    /// Panics if the substitution is not a an assignment.
    pub fn to_smt_model(&self) -> String {
        let mut buf = String::with_capacity(1024); // Pre-allocate a buffer with some estimated capacity
        buf.push('(');

        for (var, val) in self.iter() {
            assert!(val.is_constant(), "Expected a constant value");
            writeln!(
                buf,
                "\t(define-fun {} () {} {})",
                var.name(),
                var.sort(),
                val
            )
            .unwrap(); // Unwrap is safe here because writing to a String never fails
        }

        buf.push(')');
        buf
    }

    pub fn apply(&self, fm: Formula, ctx: &mut Context) -> Formula {
        match fm {
            Formula::False => Formula::False,
            Formula::True => Formula::True,
            Formula::Literal(lit) => {
                if let AtomType::BoolVar(v) = &lit.atom().ttype {
                    if let Some(Substitute::Bool(b)) = self.get(v) {
                        return if *b { Formula::True } else { Formula::False };
                    } else {
                        Formula::Literal(lit)
                    }
                } else {
                    Formula::Literal(self.apply_literal(lit, ctx))
                }
            }
            Formula::And(rs) => {
                let mut new_rs = Vec::new();
                for r in rs {
                    new_rs.push(self.apply(r, ctx));
                }
                ctx.ir_builder().and(new_rs)
            }
            Formula::Or(rs) => {
                let mut new_rs = Vec::new();
                for r in rs {
                    new_rs.push(self.apply(r, ctx));
                }
                ctx.ir_builder().or(new_rs)
            }
        }
    }

    pub fn apply_literal(&self, lit: Literal, ctx: &mut Context) -> Literal {
        let pol = lit.polarity();
        let new_atom = match &lit.atom().ttype {
            AtomType::InRe(inre) => {
                let new_p = self.apply_pattern(inre.pattern());
                ctx.ir_builder().in_re(new_p, inre.re().clone())
            }
            AtomType::WordEquation(weq) => {
                let new_l = self.apply_pattern(&weq.lhs());
                let new_r = self.apply_pattern(&weq.rhs());
                ctx.ir_builder().word_equation(new_l, new_r)
            }
            AtomType::LinearConstraint(lc) => {
                let new_l = self.apply_arith_term(lc.lhs());
                ctx.ir_builder()
                    .linear_constraint(new_l, lc.typ(), lc.rhs())
            }
            AtomType::BoolVar(bv) => ctx.ir_builder().bool_var(bv.clone()),
            AtomType::PrefixOf(_) => todo!(),
            AtomType::SuffixOf(_) => todo!(),
            AtomType::Contains(_) => todo!(),
        };
        Literal::new(new_atom, pol)
    }

    fn apply_pattern(&self, pat: &Pattern) -> Pattern {
        let mut new_pat = Pattern::empty();
        for s in pat.iter() {
            match s {
                Symbol::Constant(c) => new_pat.push(Symbol::Constant(c.clone())),
                Symbol::Variable(v) => match self.get(v) {
                    Some(Substitute::String(p)) => new_pat.extend(p.clone()),
                    None => {
                        new_pat.push_var(v.clone());
                    }
                    _ => panic!("Expected a string term"),
                },
            }
        }
        new_pat
    }

    fn apply_arith_term(&self, term: &LinearArithTerm) -> LinearArithTerm {
        let mut new_term = LinearArithTerm::new();
        for s in term.iter() {
            match s {
                LinearSummand::Const(c) => new_term.add_summand(LinearSummand::Const(*c)),
                LinearSummand::Mult(v, c) => match v {
                    VariableTerm::Int(intvar) => match self.get(intvar) {
                        Some(Substitute::Int(t)) => {
                            for s2 in t.iter() {
                                new_term.add_summand(s2.multiply(*c))
                            }
                        }
                        Some(Substitute::String(_)) | Some(Substitute::Bool(_)) => {
                            unreachable!("Expected an int term")
                        }
                        None => new_term.add_summand(s.clone()),
                    },
                    VariableTerm::Len(strvar) => match self.get(strvar) {
                        Some(Substitute::String(p)) => {
                            let int_term = Self::pattern_to_len(p);
                            for s2 in int_term.iter() {
                                new_term.add_summand(s2.multiply(*c))
                            }
                        }
                        Some(Substitute::Int(_)) | Some(Substitute::Bool(_)) => {
                            unreachable!("Expected a string term")
                        }

                        None => new_term.add_summand(s.clone()),
                    },
                },
            }
        }
        new_term.normalize();
        new_term
    }

    /// Extends this substitution with the given substitution.
    /// If the given substitution defines variables that are already defined in this substitution, the new value will overwrite the old value.
    /// Returns a list of tuples of the overwritten variables and their old values.
    pub(crate) fn extend(&mut self, other: &VarSubstitution) -> Vec<(Variable, Substitute)> {
        let mut overwrite = Vec::new();
        for (var, val) in other.iter() {
            if let Some(o) = self.set(var.clone(), val.clone()) {
                overwrite.push((var.clone(), o));
            }
        }
        overwrite
    }
}

pub trait Substitutable {
    fn apply_substitution(&self, sub: &VarSubstitution) -> Self;
}

impl Display for VarSubstitution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for (var, val) in &self.subs {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{} -> {}", var, val)?;
        }
        Ok(())
    }
}
