use super::{PredicateEncoder, SubstitutionEncoding, VariableBounds, WordEquationEncoder};
use crate::model::words::WordEquation;
use crate::sat::{pvar, Cnf};

pub struct WoorpjeEncoder {
    equation: WordEquation,
}

impl WoorpjeEncoder {}

impl PredicateEncoder for WoorpjeEncoder {
    fn is_incremental(&self) -> bool {
        false
    }

    fn reset(&self) -> bool {
        todo!()
    }

    fn encode(&self, bounds: &VariableBounds, substitution: &SubstitutionEncoding) -> Cnf {
        todo!()
    }
}

impl WordEquationEncoder for WoorpjeEncoder {
    fn new(equation: WordEquation) -> Self {
        Self { equation }
    }
}
