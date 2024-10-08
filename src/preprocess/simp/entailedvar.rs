use crate::{
    context::Context,
    ir::{AtomType, Literal, VarSubstitution},
};

use super::{RewriteSimplifier, Simplifier};

/// Finds entailed boolean variables and replaces them with their values.
pub struct EntailedBooleanVars;
impl Simplifier for EntailedBooleanVars {
    fn name(&self) -> &'static str {
        "EntailedBooleanVars"
    }
}
impl RewriteSimplifier for EntailedBooleanVars {
    fn infer(&self, lit: &Literal, entailed: bool, _: &mut Context) -> Option<VarSubstitution> {
        if entailed {
            let pol = lit.polarity();
            let atom = lit.atom();
            if let AtomType::BoolVar(v) = atom.get_type() {
                let mut subst = VarSubstitution::default();
                subst.set_bool(v.as_ref().clone(), pol);
                return Some(subst);
            }
        }
        None
    }
}
