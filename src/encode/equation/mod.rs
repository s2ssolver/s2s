mod assign;
mod weq;
// mod iwoorpje;
mod vareq;

// mod woorpje;
use weq::WordEquationEncoder;

// use crate::model::constraints::WordEquation;

use crate::repr::ir::WordEquation;

use self::{assign::AssignmentEncoder, vareq::VareqEncoder};

use super::LiteralEncoder;

pub fn get_encoder(equation: &WordEquation, pol: bool) -> Box<dyn LiteralEncoder> {
    // Both constants => panic
    if equation.lhs().is_constant() && equation.rhs().is_constant() {
        panic!("Both sides of the equation are constants. This is not supported.");
    } else if equation.lhs().is_variable() && equation.rhs().is_variable() {
        // Both single variables => Vareq
        let lhs = equation.lhs().as_variable().unwrap();
        let rhs = equation.rhs().as_variable().unwrap();
        return Box::new(VareqEncoder::new(&lhs, &rhs, pol));
    } else if equation.lhs().is_variable() && equation.rhs().is_constant() {
        // Left side variable and right side constants => Assignment
        let lhs = equation.lhs().as_variable().unwrap();
        let rhs = equation.rhs().as_constant().unwrap().chars().collect();
        return Box::new(AssignmentEncoder::new(lhs, rhs, pol));
    } else if equation.lhs().is_constant() && equation.rhs().is_variable() {
        // Symmetric case
        let lhs = equation.lhs().as_constant().unwrap().chars().collect();
        let rhs = equation.rhs().as_variable().unwrap();
        return Box::new(AssignmentEncoder::new(rhs, lhs, pol));
    } else {
        // General case
        Box::new(WordEquationEncoder::new(equation.clone(), pol))
    }
}
