use crate::{error::Error, model::constraints::RegularConstraint};

use super::ConstraintEncoder;

mod nfa;

pub use nfa::NFAEncoder;

pub trait RegularConstraintEncoder: ConstraintEncoder {
    fn new(re_constraint: RegularConstraint) -> Result<Self, Error>
    where
        Self: Sized;
}
