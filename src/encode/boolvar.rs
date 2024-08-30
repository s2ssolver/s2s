use std::rc::Rc;

use crate::{
    bounds::Bounds,
    repr::{Sorted, Variable},
    sat::{nlit, plit},
};

use super::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder};

pub struct BoolVarEncoder {
    encoded: bool,
    var: Rc<Variable>,
    pol: bool,
}

impl BoolVarEncoder {
    pub fn new(boolvar: &Rc<Variable>, pol: bool) -> Self {
        assert!(boolvar.sort().is_bool());

        Self {
            encoded: false,
            var: boolvar.clone(),
            pol,
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
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.encoded {
            Ok(EncodingResult::Trivial(true))
        } else {
            let v = dom.bool().get(&self.var).unwrap();
            let lit = if self.pol { plit(v) } else { nlit(v) };
            self.encoded = true;
            Ok(EncodingResult::cnf(vec![vec![lit]]))
        }
    }
}
