use indexmap::IndexMap;
use std::collections::HashMap;
use std::fmt::{Display, Write};

use crate::{
    ast::{Sort, Sorted, Variable},
    context::Context,
};

use super::{
    int::Summand, string::Symbol, AtomType, Formula, FormulaBuilder, LinearArithTerm, Pattern,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Substitute {
    String(Pattern),
    Int(LinearArithTerm),
}

impl Substitute {
    pub fn is_constant(&self) -> bool {
        match self {
            Self::String(p) => p.is_constant(),
            Self::Int(t) => t.reduce_constant().is_some(),
        }
    }
}

impl Display for Substitute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::String(p) => write!(f, "{}", p),
            Self::Int(t) => write!(f, "{}", t),
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

    pub fn set(&mut self, var: &Variable, term: Substitute, ctx: &Context) {
        self.subs.insert(var.clone(), term.clone());
        if var.sort() == Sort::String {
            // Also define the substitution for the length variable
            let len_var = ctx.get_len_var(var).as_ref().clone();
            let len_term = Self::strterm_to_len(&term, ctx);
            self.subs.insert(len_var, len_term);
        }
    }

    fn strterm_to_len(t: &Substitute, ctx: &Context) -> Substitute {
        if let Substitute::String(pat) = t {
            let mut vs = HashMap::new();
            let mut r = 0;
            for s in pat.iter() {
                match s {
                    Symbol::Constant(_) => r += 1,
                    Symbol::Variable(v) => {
                        let lv = ctx.get_len_var(v);
                        *vs.entry(lv.clone()).or_insert(0) += 1;
                    }
                }
            }
            let mut term = LinearArithTerm::new();
            vs.into_iter()
                .for_each(|(v, c)| term.add_var_coeff(v.as_ref(), c));
            term.add_summand(Summand::Const(r));

            Substitute::Int(term)
        } else {
            panic!("Expected a string term")
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Substitute)> {
        self.subs.iter()
    }

    /// Calculates the composition of two substitutions.
    /// The result is the substitution that results from applying the given substitution to this substitution.
    /// If the given substitution defines variables that are not defined in this substitution, the result will contain these variables.
    pub fn compose(&self, other: &Self, ctx: &Context) -> Self {
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
            };
            sub.set(var, chained, ctx);
        }
        for (var, val) in &other.subs {
            // Add the substitution if it is not yet present
            if sub.get(var).is_none() {
                sub.set(var, val.clone(), ctx);
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

    pub fn apply(&self, fm: Formula, builder: &mut FormulaBuilder) -> Formula {
        match fm {
            Formula::Literal(lit) => {
                let pol = lit.polarity();
                let new_lit = match &lit.atom().ttype {
                    AtomType::InRe(p, r) => {
                        let new_p = self.apply_pattern(&p);
                        let new_in_re = builder.in_re(new_p, r.clone());
                        builder.literal(new_in_re, pol)
                    }
                    AtomType::WordEquation(l, r) => {
                        let new_l = self.apply_pattern(&l);
                        let new_r = self.apply_pattern(&r);
                        let new_eq = builder.word_equation(new_l, new_r);
                        builder.literal(new_eq, pol)
                    }
                    AtomType::LinearConstraint(l, o, r) => {
                        let new_l = self.apply_arith_term(&l);
                        let new_eq = builder.linear_constraint(new_l, *o, *r);
                        builder.literal(new_eq, pol)
                    }
                    AtomType::BoolVar(bv) => {
                        let v = builder.bool_var(bv.clone());
                        builder.literal(v, pol)
                    }
                    AtomType::BoolConst(b) => {
                        let v = builder.bool_const(*b);
                        builder.literal(v, pol)
                    }
                    AtomType::PrefixOf(_, _) => todo!(),
                    AtomType::SuffixOf(_, _) => todo!(),
                    AtomType::Contains(_, _) => todo!(),
                };
                new_lit
            }
            Formula::And(rs) => {
                let mut new_rs = Vec::new();
                for r in rs {
                    new_rs.push(self.apply(r, builder));
                }
                builder.and(new_rs)
            }
            Formula::Or(rs) => {
                let mut new_rs = Vec::new();
                for r in rs {
                    new_rs.push(self.apply(r, builder));
                }
                builder.or(new_rs)
            }
        }
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
                Summand::Const(c) => new_term.add_summand(Summand::Const(*c)),
                Summand::VarCoeff(v, c) => match self.get(v) {
                    Some(Substitute::Int(t)) => {
                        for s2 in t.iter() {
                            new_term.add_summand(s2.multiply(*c))
                        }
                    }
                    None => new_term.add_var_coeff(v, *c),
                    _ => panic!("Expected an integer term"),
                },
            }
        }
        new_term.normalize();
        new_term
    }
}
