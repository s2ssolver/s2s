mod assign;
// mod weq_old;
// mod iwoorpje;
mod vareq;
mod weq;

use weq::{WordEquationEncoder, WordInEquationEncoder};
// mod woorpje;

// use crate::model::constraints::WordEquation;

use crate::node::canonical::WordEquation;

use self::{assign::AssignmentEncoder, vareq::VareqEncoder};

use super::LiteralEncoder;

pub fn get_encoder(equation: &WordEquation, pol: bool) -> Box<dyn LiteralEncoder> {
    // Both constants => panic
    match equation {
        WordEquation::ConstantEquality(_, _) => {
            panic!("Constant equations cannot be encoded: {}", equation)
        }
        WordEquation::VarEquality(lhs, rhs) => Box::new(VareqEncoder::new(lhs, rhs, pol)),
        WordEquation::VarAssignment(lhs, rhs) => Box::new(AssignmentEncoder::new(
            lhs.clone(),
            rhs.chars().collect(),
            pol,
        )),
        WordEquation::General(_, _) => {
            if pol {
                Box::new(WordEquationEncoder::new(equation.clone()))
            } else {
                Box::new(WordInEquationEncoder::new(equation.clone()))
            }
        } //Box::new(WordEquationEncoderOld::new(equation.clone(), pol)),
    }
}
