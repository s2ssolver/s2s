//! Implementation of the automaton-based encoding of regular constraints.
//! The encoding was first introduced in the paper
//!
//! > Kulczynski, M., Lotz, K., Nowotka, D., Poulsen, D.B. (2022). *Solving String Theories Involving Regular Membership Predicates Using SAT*. In: Legunsen, O., Rosu, G. (eds) Model Checking Software. SPIN 2022. Lecture Notes in Computer Science, vol 13255. Springer, Cham. https://doi.org/10.1007/978-3-031-15077-7_8
//!
//! This module contains the enhanced version of the encoding, which allows for incremental solving. This version is described in the paper
//!
//! > TODO: Add CAV paper reference

use crate::{
    bounds::Bounds,
    encode::{domain::DomainEncoding, ConstraintEncoder, EncodingResult},
    model::constraints::RegularConstraint,
};

use super::RegularConstraintEncoder;

pub struct NFAEncoder {
    constraint: RegularConstraint,
}

impl NFAEncoder {}

impl ConstraintEncoder for NFAEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(&mut self, _bounds: &Bounds, _substitution: &DomainEncoding) -> EncodingResult {
        // Make sure automaton is compiled
        let _ = self.constraint.compile();

        todo!()
    }
}

impl RegularConstraintEncoder for NFAEncoder {
    fn new(con: RegularConstraint) -> Self {
        Self { constraint: con }
    }
}
