//! Applies Levi's rule to simplify word equations.

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, Pattern, Substitutable, Symbol, VarSubstitution, WordEquation},
};

use super::{LiteralSimplifier, SimplificationResult};

#[derive(Clone, Default)]
pub(super) struct LevisSimp;

impl LevisSimp {
    fn strip_common_prefix(weq: &WordEquation) -> Option<WordEquation> {
        let mut i = 0;
        let lhs = weq.lhs();
        let rhs = weq.rhs();
        while i < lhs.len() && i < rhs.len() && lhs[i] == rhs[i] {
            i += 1;
        }
        if i > 0 {
            Some(WordEquation::new(lhs.strip_prefix(i), rhs.strip_prefix(i)))
        } else {
            None
        }
    }

    fn strip_common_suffix(weq: &WordEquation) -> Option<WordEquation> {
        let mut i = 0;
        let lhs = weq.lhs();
        let rhs = weq.rhs();
        while i < lhs.len() && i < rhs.len() && lhs[lhs.len() - i - 1] == rhs[rhs.len() - i - 1] {
            i += 1;
        }
        if i > 0 {
            Some(WordEquation::new(lhs.strip_suffix(i), rhs.strip_suffix(i)))
        } else {
            None
        }
    }

    /// Applies Levi's rule to simplify the given word equation.
    fn levis_step(weq: &WordEquation) -> SimplificationResult<WordEquation> {
        // Strip all common prefixes
        let reduced = Self::strip_common_prefix(&weq);
        let weq = reduced.unwrap_or_else(|| weq.clone());
        let lhs = weq.lhs();
        let rhs = weq.rhs();
        let mut subst = VarSubstitution::default();
        match (lhs.first(), rhs.first()) {
            /* One side is constant, the other variable */
            (Some(Symbol::Constant(c)), Some(Symbol::Variable(v)))
            | (Some(Symbol::Variable(v)), Some(Symbol::Constant(c))) => {
                let mut substitutee = Pattern::constant(&String::from(*c));
                substitutee.push_var(v.clone());
                subst.set_str(v.clone(), substitutee);
                let lhs_new = lhs.apply_substitution(&subst);
                let rhs_new = rhs.apply_substitution(&subst);
                let mut applied_weq = WordEquation::new(lhs_new, rhs_new);
                // Strip common prefixes again, there is now at least one
                applied_weq = Self::strip_common_prefix(&applied_weq).unwrap_or(applied_weq);
                SimplificationResult::Simplified(applied_weq, subst)
            }

            // All other cases are either not reducible or already reduced by stripping common prefixes
            _ => SimplificationResult::Unchanged,
        }
    }

    fn apply_levis(weq: &WordEquation) -> SimplificationResult<WordEquation> {
        let (mut simped, mut subst) = match Self::levis_step(weq) {
            SimplificationResult::Simplified(simped, subst) => (simped, subst),
            SimplificationResult::Trivial(t) => return SimplificationResult::Trivial(t),
            SimplificationResult::Unchanged => return SimplificationResult::Unchanged,
        };

        // Apply until no more simplifications are possible
        let mut applied = true;
        while applied {
            applied = false;
            match Self::levis_step(&simped) {
                SimplificationResult::Simplified(f, subst_new) => {
                    applied = true;
                    subst = subst.compose(&subst_new);
                    simped = f;
                }
                SimplificationResult::Trivial(t) => return SimplificationResult::Trivial(t),
                SimplificationResult::Unchanged => (),
            }
        }
        let result = SimplificationResult::Simplified(simped, subst);

        result
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

impl LiteralSimplifier for LevisSimp {
    fn simplify(
        &self,
        lit: &Literal,
        entailed: bool,
        ctx: &mut Context,
    ) -> SimplificationResult<Literal> {
        let pol = lit.polarity();
        if let AtomType::WordEquation(weq) = lit.atom().get_type() {
            if pol && entailed {
                // we can apply Levi's rule until no more simplifications are possible
                match Self::apply_levis(weq) {
                    SimplificationResult::Simplified(simped, mut subs) => {
                        // also apply it to the reverse equation
                        let reversed = simped.reverse();
                        match Self::apply_levis(&reversed) {
                            SimplificationResult::Simplified(simped_rev, subs_rev) => {
                                // reverse the substitutions
                                let subs_rev = Self::reverse_subsitutions(subs_rev);
                                subs = subs.compose(&subs_rev);
                                // reverse the equation back
                                let simped = simped_rev.reverse();
                                let as_atom = ctx
                                    .ir_builder()
                                    .register_atom(AtomType::WordEquation(simped));
                                SimplificationResult::Simplified(Literal::new(as_atom, pol), subs)
                            }
                            SimplificationResult::Trivial(t) => SimplificationResult::Trivial(t),
                            SimplificationResult::Unchanged => {
                                // Use the (non-reversed) simplified equation
                                let as_atom = ctx
                                    .ir_builder()
                                    .register_atom(AtomType::WordEquation(simped));
                                SimplificationResult::Simplified(Literal::new(as_atom, pol), subs)
                            }
                        }
                    }
                    SimplificationResult::Trivial(t) => SimplificationResult::Trivial(t),
                    SimplificationResult::Unchanged => SimplificationResult::Unchanged,
                }
            } else {
                // we can only strip common prefixes and suffixes if the polarity is negative or the literal is not entailed
                let stripped =
                    Self::strip_common_prefix(weq).and_then(|r| Self::strip_common_suffix(&r));
                if let Some(reduced) = stripped {
                    let as_atom = ctx
                        .ir_builder()
                        .register_atom(AtomType::WordEquation(reduced));
                    SimplificationResult::Simplified(
                        Literal::new(as_atom, pol),
                        VarSubstitution::default(),
                    )
                } else {
                    SimplificationResult::Unchanged
                }
            }
        } else {
            SimplificationResult::Unchanged
        }
    }
}
