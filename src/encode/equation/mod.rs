mod assign;
mod weq;
// mod iwoorpje;
mod vareq;

// mod woorpje;
use weq::WordEquationEncoder;

// use crate::model::constraints::WordEquation;

use crate::ir::WordEquation;

use self::{assign::AssignmentEncoder, vareq::VareqEncoder};

use super::LiteralEncoder;

pub fn get_encoder(equation: &WordEquation, pol: bool) -> Box<dyn LiteralEncoder> {
    // Both constants => panic
    match equation {
        WordEquation::ConstantEquality(_, _) => panic!("Constant equations cannot be encoded"),
        WordEquation::VarEquality(lhs, rhs) => return Box::new(VareqEncoder::new(lhs, rhs, pol)),
        WordEquation::VarAssignment(lhs, rhs) => Box::new(AssignmentEncoder::new(
            lhs.clone(),
            rhs.chars().collect(),
            pol,
        )),
        WordEquation::General(_, _) => Box::new(WordEquationEncoder::new(equation.clone(), pol)),
    }
}
