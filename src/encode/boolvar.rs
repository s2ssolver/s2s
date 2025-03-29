use std::rc::Rc;

use rustsat::instances::Cnf;

use crate::{
    domain::Domain,
    node::{Sorted, Variable},
    sat::{nlit, plit},
};

use super::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink};

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

impl EncodeLiteral for BoolVarEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        self.encoded = false;
    }

    fn encode(
        &mut self,
        _: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        if !self.encoded {
            let v = dom_enc.bool().get(&self.var).unwrap();
            let lit = if self.pol { plit(v) } else { nlit(v) };
            self.encoded = true;
            let mut cnf = Cnf::new();
            cnf.add_unit(lit);
            sink.add_cnf(cnf);
        }
        Ok(())
    }
}
