use crate::{
    encode::{ConstraintEncoder, EncodingResult},
    error::Error,
    model::constraints::WordEquation,
};

///! Encoder for `assignment` type equations.
///! Assignments are of the form `x = w` where `x` is a variable and `w` is a constant word.

pub struct AssignmentEncoder {}

impl AssignmentEncoder {
    #[allow(dead_code)]
    pub fn new(_equation: WordEquation) -> Self {
        Self {}
    }
}

impl ConstraintEncoder for AssignmentEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        _bounds: &crate::bounds::Bounds,
        _substitution: &crate::encode::domain::DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        todo!()
    }
}
