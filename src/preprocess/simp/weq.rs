//! Simplification rules for word equations.

use crate::{
    context::Context,
    repr::ir::{AtomType, Literal, WordEquation},
};

use super::{PureSimplifier, Simplifier};

/// Removes common prefixes and suffixes from word equations.
pub struct StripCommonPrefixSuffix;
impl StripCommonPrefixSuffix {
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
    fn strip(weq: &WordEquation) -> Option<WordEquation> {
        match Self::strip_common_prefix(weq) {
            Some(s) => Self::strip_common_suffix(&s),
            None => Self::strip_common_suffix(weq),
        }
    }
}
impl Simplifier for StripCommonPrefixSuffix {
    fn name(&self) -> &'static str {
        "WeqStripCommonPrefixSuffix"
    }
}
impl PureSimplifier for StripCommonPrefixSuffix {
    fn simplify(&self, lit: &Literal, _entailed: bool, ctx: &mut Context) -> Option<Literal> {
        if let AtomType::WordEquation(weq) = lit.atom().get_type() {
            let stripped = Self::strip(weq)?;
            let atom = ctx
                .ir_builder()
                .register_atom(AtomType::WordEquation(stripped));
            Some(Literal::new(atom, lit.polarity()))
        } else {
            None
        }
    }
}
