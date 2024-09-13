//! Applies Levi's rule to simplify word equations.

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, Pattern, Symbol, VarSubstitution, WordEquation},
};

use super::{RewriteSimplifier, Simplifier};

#[derive(Clone, Default)]
pub(super) struct LevisSimp;

impl LevisSimp {
    /// Applies Levi's rule to simplify the given word equation.
    fn levis_step(weq: &WordEquation) -> Option<VarSubstitution> {
        // Strip all common prefixes

        let lhs = weq.lhs();
        let rhs = weq.rhs();

        // Helper function to check if we have "a\beta = Y\alpha" or "Y\alpha = a\beta" and Y cannot be set to the empty string
        fn not_empty(constant: &char, pattern: &Pattern) -> bool {
            let scnd = pattern.at(1);
            match scnd {
                Some(Symbol::Constant(c)) => c != constant,
                None => true,
                _ => false,
            }
        }

        match (lhs.first(), rhs.first()) {
            /* One side is constant, the other variable */
            (Some(Symbol::Constant(c)), Some(Symbol::Variable(v))) if not_empty(c, &rhs) => {
                let mut subst = VarSubstitution::default();
                let mut substitutee = Pattern::constant(&String::from(*c));
                substitutee.push_var(v.clone());
                subst.set_str(v.clone(), substitutee);
                Some(subst)
            }
            (Some(Symbol::Variable(v)), Some(Symbol::Constant(c))) if not_empty(c, &lhs) => {
                let mut subst = VarSubstitution::default();
                let mut substitutee = Pattern::constant(&String::from(*c));
                substitutee.push_var(v.clone());
                subst.set_str(v.clone(), substitutee);
                Some(subst)
            }
            // All other cases are either not reducible or already reduced by stripping common prefixes
            _ => return None,
        }
    }

    fn reverse_subsitutions(subs: VarSubstitution) -> VarSubstitution {
        let mut reversed = VarSubstitution::default();
        for (k, v) in subs.iter() {
            let revd = v.as_string().reversed();
            reversed.set_str(k.clone(), revd);
        }
        reversed
    }
}
impl Simplifier for LevisSimp {
    fn name(&self) -> &'static str {
        "Levis Lemma"
    }
}
impl RewriteSimplifier for LevisSimp {
    fn infer(&self, lit: &Literal, entailed: bool, _ctx: &mut Context) -> Option<VarSubstitution> {
        if entailed && lit.polarity() {
            if let AtomType::WordEquation(weq) = lit.atom().get_type() {
                let res = Self::levis_step(weq);
                if res.is_some() {
                    return res;
                } else {
                    // try to reverse the equation and apply the rule again
                    let reversed = weq.reversed();
                    let reversed_simp = Self::levis_step(&reversed)?;
                    Some(Self::reverse_subsitutions(reversed_simp))
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}
