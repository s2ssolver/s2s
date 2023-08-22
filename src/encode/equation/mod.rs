mod alignment;
mod assign;
mod iwoorpje;
mod vareq;
mod woorpje;
use alignment::AlignmentEncoder;

use crate::model::constraints::WordEquation;

use self::vareq::VareqEncoder;

use super::ConstraintEncoder;

pub fn get_encoder(equation: &WordEquation) -> Box<dyn ConstraintEncoder> {
    match equation {
        WordEquation::VarEquality { lhs, rhs, eq_type } => {
            Box::new(VareqEncoder::new(lhs, rhs, eq_type.is_equality()))
        }
        WordEquation::Generic { .. } | WordEquation::Assignment { .. } => {
            Box::new(AlignmentEncoder::new(equation.clone()))
        }
    }
}
