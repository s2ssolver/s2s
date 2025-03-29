mod assign;
// mod weq_old;
// mod iwoorpje;
mod vareq;
mod weq;

pub use weq::{WordEquationEncoder, WordInEquationEncoder};
// mod woorpje;

// use crate::model::constraints::WordEquation;

use crate::node::canonical::WordEquation;

pub use self::{assign::AssignmentEncoder, vareq::VareqEncoder};

use super::EncodeLiteral;

pub enum WEQEncoder {
    /// The encoder for word equations
    WordEquation(WordEquationEncoder),
    /// The encoder for word in equations
    WordInEquation(WordInEquationEncoder),

    /// The encoder for variable equations
    Vareq(VareqEncoder),

    /// The encoder for assignment equations
    Assignment(AssignmentEncoder),
}

impl EncodeLiteral for WEQEncoder {
    fn encode(
        &mut self,
        dom: &crate::domain::Domain,
        dom_enc: &super::domain::DomainEncoding,
        sink: &mut impl super::EncodingSink,
    ) -> Result<(), super::EncodingError> {
        match self {
            WEQEncoder::WordEquation(encoder) => encoder.encode(dom, dom_enc, sink),
            WEQEncoder::WordInEquation(encoder) => encoder.encode(dom, dom_enc, sink),
            WEQEncoder::Vareq(encoder) => encoder.encode(dom, dom_enc, sink),
            WEQEncoder::Assignment(encoder) => encoder.encode(dom, dom_enc, sink),
        }
    }
}
pub fn get_encoder(equation: &WordEquation, pol: bool) -> WEQEncoder {
    // Both constants => panic
    match equation {
        WordEquation::ConstantEquality(_, _) => {
            panic!("Constant equations cannot be encoded: {}", equation)
        }
        WordEquation::VarEquality(lhs, rhs) => WEQEncoder::Vareq(VareqEncoder::new(lhs, rhs, pol)),
        WordEquation::VarAssignment(lhs, rhs) => {
            WEQEncoder::Assignment(AssignmentEncoder::new(lhs.clone(), rhs.clone(), pol))
        }
        WordEquation::General(_, _) => {
            if pol {
                WEQEncoder::WordEquation(WordEquationEncoder::new(equation.clone()))
            } else {
                WEQEncoder::WordInEquation(WordInEquationEncoder::new(equation.clone()))
            }
        } //Box::new(WordEquationEncoderOld::new(equation.clone(), pol)),
    }
}
