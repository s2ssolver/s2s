//! Conversion of formulas to normal form.
//! We say that a formula is in normal form if it is a conjunction of literals, where each atom is either
//! - a word equation,
//! - a regular membership constraint, or
//! - a linear constraint.
use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;
use regulaer::re::{ReBuilder, Regex};

use crate::{
    context::Context,
    repr::ir::{AtomType, Formula, Literal, Pattern},
    repr::{Sort, Variable},
};

use super::PreprocessingError;

#[derive(Default)]
pub struct Normalizer {
    rewrites: HashMap<Literal, Formula>,
    identities: HashMap<Pattern, Rc<Variable>>,
}

impl Normalizer {
    pub fn rewrite(
        &mut self,
        formula: Formula,
        ctx: &mut Context,
    ) -> Result<Formula, PreprocessingError> {
        self.reset();

        let rewritten = self.rewrite_formula(formula, ctx)?;

        // Create a word equation for each identity
        let identity_eqs = self
            .identities
            .iter()
            .map(|(p, v)| {
                let eq = ctx
                    .ir_builder()
                    .word_equation(p.clone(), Pattern::variable(v.as_ref()));
                ctx.ir_builder().plit(eq)
            })
            .collect_vec();

        if identity_eqs.is_empty() {
            Ok(rewritten)
        } else {
            // Append the identity equations to the rewritten formula
            let mut conjuncts = vec![rewritten];
            conjuncts.extend(identity_eqs);
            Ok(ctx.ir_builder().and(conjuncts))
        }
    }

    fn rewrite_formula(
        &mut self,
        formula: Formula,
        ctx: &mut Context,
    ) -> Result<Formula, PreprocessingError> {
        // TODO: Check if error type is "Unsupported" and replace with neutral element in order to generate an under-approximation of the formula
        match formula {
            Formula::Literal(lit) => self.rewrite_literal(lit, ctx),
            Formula::And(es) => {
                let formulas = es
                    .iter()
                    .map(|e| self.rewrite_formula(e.clone(), ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.ir_builder().and(formulas))
            }
            Formula::Or(es) => {
                let formulas = es
                    .iter()
                    .map(|e| self.rewrite_formula(e.clone(), ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.ir_builder().or(formulas))
            }
            Formula::True => Ok(Formula::True),
            Formula::False => Ok(Formula::False),
        }
    }

    fn rewrite_literal(
        &mut self,
        lit: Literal,
        ctx: &mut Context,
    ) -> Result<Formula, PreprocessingError> {
        if let Some(rewrite) = self.rewrites.get(&lit) {
            Ok(rewrite.clone())
        } else {
            let pol = lit.polarity();
            match lit.atom().get_type() {
                AtomType::InRe(inre) if !inre.pattern().is_variable() => {
                    let lhs = inre.pattern();
                    let rhs = inre.re();
                    let v = if let Some(v) = self.identities.get(&lhs) {
                        v.clone()
                    } else {
                        let v = ctx.new_temp_var(Sort::String);
                        self.identities.insert(lhs.clone(), v.clone());
                        v
                    };
                    let v_pat = Pattern::variable(v.as_ref());
                    let new_in_re = ctx.ir_builder().in_re(v_pat, rhs.clone());
                    let new_lit = ctx.ir_builder().literal(new_in_re, pol);
                    self.rewrites.insert(lit, new_lit.clone());
                    Ok(new_lit)
                }
                AtomType::PrefixOf(pr) if pr.prefix().is_constant() => {
                    let pref = pr.prefix().as_constant().unwrap();
                    let of = pr.of();
                    let re = self.prefix_re(&pref, ctx);
                    let as_re = ctx.ir_builder().in_re(of.clone(), re);
                    let new_lit = ctx.ir_builder().literal(as_re, pol);
                    // Give it another pass because the new literal might still need rewriting
                    let cleaned = self.rewrite_formula(new_lit, ctx)?;
                    self.rewrites.insert(lit, cleaned.clone());
                    Ok(cleaned)
                }
                AtomType::PrefixOf(pr) => {
                    if pol {
                        let w2 = ctx.new_temp_var(Sort::String);
                        let mut rhs = pr.prefix().clone();
                        rhs.push_var(w2.as_ref().clone());
                        let eq = ctx.ir_builder().word_equation(pr.of().clone(), rhs);
                        let new_lit = ctx.ir_builder().plit(eq);
                        self.rewrites.insert(lit, new_lit.clone());
                        Ok(new_lit)
                    } else {
                        Err(PreprocessingError::InvalidNegationQuantifier(
                            lit.to_string(),
                        ))
                    }
                }
                AtomType::SuffixOf(suf) if suf.suffix().is_constant() => {
                    let suffix = suf.suffix().as_constant().unwrap();
                    let re = self.suffix_re(&suffix, ctx);
                    let as_re = ctx.ir_builder().in_re(suf.of().clone(), re);
                    let new_lit = ctx.ir_builder().literal(as_re, pol);
                    // Give it another pass because the new literal might still need rewriting
                    let cleaned = self.rewrite_formula(new_lit, ctx)?;
                    self.rewrites.insert(lit, cleaned.clone());
                    Ok(cleaned)
                }
                AtomType::SuffixOf(suf) => {
                    if pol {
                        let w2 = ctx.new_temp_var(Sort::String);
                        let mut rhs = Pattern::variable(w2.as_ref());
                        rhs.concat(suf.suffix().clone());
                        let eq = ctx.ir_builder().word_equation(suf.of().clone(), rhs);
                        let new_lit = ctx.ir_builder().plit(eq);
                        self.rewrites.insert(lit, new_lit.clone());
                        Ok(new_lit)
                    } else {
                        Err(PreprocessingError::InvalidNegationQuantifier(
                            lit.to_string(),
                        ))
                    }
                }
                AtomType::Contains(con) if con.needle().is_constant() => {
                    let needle = con.needle().as_constant().unwrap();
                    let re = self.contains_re(&needle, ctx);
                    let as_re = ctx.ir_builder().in_re(con.haystack().clone(), re);
                    let new_lit = ctx.ir_builder().literal(as_re, pol);
                    // Give it another pass because the new literal might still need rewriting
                    let cleaned = self.rewrite_formula(new_lit, ctx)?;
                    self.rewrites.insert(lit, cleaned.clone());
                    Ok(cleaned)
                }
                AtomType::Contains(con) => {
                    if pol {
                        let w2 = ctx.new_temp_var(Sort::String);
                        let w3 = ctx.new_temp_var(Sort::String);
                        let mut rhs = Pattern::variable(w2.as_ref());
                        rhs.concat(con.needle().clone());
                        rhs.push_var(w3.as_ref().clone());
                        let eq = ctx.ir_builder().word_equation(con.haystack().clone(), rhs);
                        let new_lit = ctx.ir_builder().plit(eq);
                        self.rewrites.insert(lit, new_lit.clone());
                        Ok(new_lit)
                    } else {
                        Err(PreprocessingError::InvalidNegationQuantifier(
                            lit.to_string(),
                        ))
                    }
                }
                AtomType::LinearConstraint(lc) => {
                    // Linear constraints are in normal form by design
                    // We only need to ensure that the polarity is correct and that the lhs is canonical
                    assert!(lit.polarity());
                    let mut lhs = lc.lhs().clone();
                    lhs.canonicalize();
                    let atom = ctx
                        .ir_builder()
                        .linear_constraint(lhs, lc.operator(), lc.rhs());
                    Ok(ctx.ir_builder().plit(atom))
                }
                _ => Ok(Formula::Literal(lit)), // No rewrite required
            }
        }
    }

    fn reset(&mut self) {
        self.rewrites.clear();
    }

    /// Creates a regular expression that matches all strings with the given prefix.
    fn prefix_re(&self, prefix: &str, ctx: &mut Context) -> Regex {
        let builder = ctx.ast_builder().re_builder();
        let all = builder.all();
        let pref = builder.word(prefix.into());
        builder.concat(vec![pref, all])
    }

    /// Creates a regular expression that matches all strings with the given suffix.
    fn suffix_re(&self, suffix: &str, ctx: &mut Context) -> Regex {
        let builder = ctx.ast_builder().re_builder();
        let all = builder.all();
        let suff = builder.word(suffix.into());
        builder.concat(vec![all, suff])
    }

    /// Creates a regular expression that matches all strings containing the given substring.
    fn contains_re(&self, needle: &str, ctx: &mut Context) -> Regex {
        let builder = ctx.ast_builder().re_builder();
        let all = builder.all();
        let needle = builder.word(needle.clone().into());
        builder.concat(vec![all.clone(), needle, all])
    }
}
