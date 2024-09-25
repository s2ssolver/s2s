use regulaer::re::{deriv::deriv_word, RegexProps, Word};

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, Pattern, VarSubstitution},
};

use super::{PureSimplifier, RewriteSimplifier, Simplifier};

/// Finds constant prefixes and suffixes of entailed regular constraints on variables.
/// That means, it derives the following substitutions:
/// - if `x \in wR` then  x -> wx
/// - if `x \in Rw` then  x -> xw
/// This interplays with [ConstantDerivation], which will subsequently strip the constant from the variable by using derivatives on the regular expressions or reduces the constant prefix/suffix constraints.
pub struct ConstantPrefixSuffix;
impl Simplifier for ConstantPrefixSuffix {
    fn name(&self) -> &'static str {
        "RegexConstantPrefixSuffix"
    }
}
impl RewriteSimplifier for ConstantPrefixSuffix {
    fn infer(&self, lit: &Literal, entailed: bool, _ctx: &mut Context) -> Option<VarSubstitution> {
        if !entailed || !lit.polarity() {
            return None;
        }
        if let AtomType::InRe(inre) = lit.atom().get_type() {
            let var = inre.pattern().as_variable()?;
            let re = inre.re();
            if let Some(pre) = re.prefix() {
                // X -> preX
                let mut pattern = Pattern::from_iter(pre.iter());
                pattern.push_var(var.clone());
                let mut subst = VarSubstitution::default();
                subst.set_str(var, pattern);
                return Some(subst);
            } else if let Some(suf) = re.suffix() {
                // X -> Xsuf
                let mut pattern = Pattern::variable(&var);
                pattern.concat(Pattern::from_iter(suf.iter()));
                let mut subst = VarSubstitution::default();
                subst.set_str(var, pattern);
                return Some(subst);
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// Removes constants prefixes of patterns in regular constraints or prefix- and suffix constraints.
/// Let $\alpha$ be a pattern and $w$ be a constant word.
/// - Regular constraints of the form $w\alpha \in R$ are replaced with $\alpha \in (w^{-1})R$
/// - Regular constraints of the for $\alpha w \in R$ are replaced with $\alpha \in rev((w^{-1})rev(R))$
/// where $(w^{-1})R$ is the regular derivative of $R$ w.r.t. $w$ and $rev(R)$ is the reverse of $R$.
pub struct ConstantDerivation;
impl Simplifier for ConstantDerivation {
    fn name(&self) -> &'static str {
        "RegexConstantDerivation"
    }
}
impl PureSimplifier for ConstantDerivation {
    fn simplify(&self, lit: &Literal, _entailed: bool, ctx: &mut Context) -> Option<Literal> {
        if let AtomType::InRe(inre) = lit.atom().get_type() {
            let mut simped = false;
            let prefix = inre.pattern().constant_prefix();
            let re = if !prefix.is_empty() {
                let w = Word::from_iter(prefix.chars());
                simped = true;
                deriv_word(inre.re(), &w, ctx.ast_builder().re_builder())
            } else {
                // we're just cloning an Rc, so it's cheap
                inre.re().clone()
            };
            let pattern = inre.pattern().strip_prefix(prefix.len());
            let suffix = pattern.constant_suffix();
            let re = if !suffix.is_empty() {
                let w = Word::from_iter(suffix.chars()).reversed();
                let rev = ctx.ast_builder().re_builder().reversed(&re);
                let rev_deriv = deriv_word(&rev, &w, ctx.ast_builder().re_builder());
                simped = true;
                // reverse back the derivative
                ctx.ast_builder().re_builder().reversed(&rev_deriv)
            } else {
                re
            };
            let pattern = pattern.strip_suffix(suffix.len());

            if simped {
                let new_inre = ctx.ir_builder().in_re(pattern, re);
                Some(Literal::new(new_inre, lit.polarity()))
            } else {
                None
            }
        } else {
            None
        }
    }
}
