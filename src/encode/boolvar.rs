use crate::{
    bounds::Bounds,
    error::Error,
    model::Variable,
    sat::{plit, nlit, PLit},
};

use super::{domain::DomainEncoding, ConstraintEncoder, EncodingResult};

pub struct BoolVarEncoder {
    encoded: bool,
    lit: PLit,
}

impl BoolVarEncoder {
    pub fn new(boolvar: Variable, pol: bool) -> Self {
        let lit = match boolvar {
            Variable::Bool { value, .. } => {
                if pol {
                    plit(value)
                } else {
                    nlit(value)
                }
            }
            _ => panic!("Expected a boolean variable, got {}", boolvar),
        };
        Self {
            encoded: false,
            lit,
        }
    }
}

impl ConstraintEncoder for BoolVarEncoder {
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
    ) -> Result<EncodingResult, Error> {
        if self.encoded {
            Ok(EncodingResult::Trivial(true))
        } else {
            self.encoded = true;
            Ok(EncodingResult::cnf(vec![vec![self.lit]]))
        }
    }
}
