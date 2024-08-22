use crate::{
    bounds::Bounds,
    context::Context,
    repr::{Sorted, Variable},
    sat::{nlit, plit, pvar, PLit},
};

use super::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder};

pub struct BoolVarEncoder {
    encoded: bool,
    lit: PLit,
}

impl BoolVarEncoder {
    pub fn new(boolvar: &Variable, pol: bool) -> Self {
        assert!(boolvar.sort().is_bool());
        // Create a new propositional variable for the boolean variable
        let v = pvar();
        let lit = if pol { plit(v) } else { nlit(v) };
        Self {
            encoded: false,
            lit,
        }
    }
}

impl LiteralEncoder for BoolVarEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        self.encoded = false;
    }

    fn encode(
        &mut self,
        _bounds: &Bounds,
        _substitution: &DomainEncoding,
        _ctx: &Context,
    ) -> Result<EncodingResult, EncodingError> {
        if self.encoded {
            Ok(EncodingResult::Trivial(true))
        } else {
            self.encoded = true;
            Ok(EncodingResult::cnf(vec![vec![self.lit]]))
        }
    }
}
