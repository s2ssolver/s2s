use crate::model::constraints::RegularConstraint;

use super::ConstraintEncoder;

mod nfa;

pub trait RegularConstraintEncoder: ConstraintEncoder {
    fn new(re_constraint: RegularConstraint) -> Self;
}
