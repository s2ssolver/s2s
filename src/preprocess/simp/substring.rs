//! Simplify for substring relations, including prefix, suffix, and containment constraints.

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, Pattern, VarSubstitution},
};

use super::{RewriteSimplifier, Simplifier};

/// Reduces entailed constant prefix- and suffix-constraints by deriving the following substitutions:
/// - if `w prefixof x` then x -> wx
/// - if `w suffixof x` then x -> wx
/// After applying the substitution, the constaints are trivially satisfied.
pub struct ConstantPrefixSuffix;
impl Simplifier for ConstantPrefixSuffix {
    fn name(&self) -> &'static str {
        "ConstantPrefixSuffixConstraints"
    }
}
impl RewriteSimplifier for ConstantPrefixSuffix {
    fn infer(&self, lit: &Literal, entailed: bool, _ctx: &mut Context) -> Option<VarSubstitution> {
        if !entailed || !lit.polarity() {
            return None;
        }
        if let AtomType::PrefixOf(prefixof) = lit.atom().get_type() {
            let var = prefixof.of().as_variable()?;
            let prefix = prefixof.prefix().as_constant()?;
            // Construct the substitution x -> wx
            let mut subst = VarSubstitution::default();
            let mut pattern = Pattern::constant(&prefix);
            pattern.push_var(var.clone());
            subst.set_str(var, pattern);
            Some(subst)
        } else if let AtomType::SuffixOf(suffixof) = lit.atom().get_type() {
            let var = suffixof.of().as_variable()?;
            let suffix = suffixof.suffix().as_constant()?;
            // Construct the substitution x -> xw
            let mut subst = VarSubstitution::default();
            let mut pattern = Pattern::variable(&var);
            pattern.concat(Pattern::constant(&suffix));
            subst.set_str(var, pattern);
            Some(subst)
        } else {
            None
        }
    }
}
