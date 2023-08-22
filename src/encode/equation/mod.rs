mod alignment;
mod assign;
mod iwoorpje;
mod vareq;
mod woorpje;
use alignment::AlignmentEncoder;

use crate::model::constraints::WordEquation;

use self::{assign::AssignmentEncoder, vareq::VareqEncoder};

use super::ConstraintEncoder;

pub fn get_encoder(equation: &WordEquation) -> Box<dyn ConstraintEncoder> {
    match equation {
        WordEquation::VarEquality { lhs, rhs, eq_type } => {
            Box::new(VareqEncoder::new(lhs, rhs, eq_type.is_equality()))
        }
        WordEquation::Assignment { lhs, rhs, eq_type } => Box::new(AssignmentEncoder::new(
            lhs.clone(),
            rhs.clone(),
            eq_type.is_equality(),
        )),
        WordEquation::Generic { .. } => Box::new(AlignmentEncoder::new(equation.clone())),
    }
}
