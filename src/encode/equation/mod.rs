mod alignment;
mod iwoorpje;
mod woorpje;
pub use alignment::AlignmentEncoder;
pub use iwoorpje::IWoorpjeEncoder;
pub use woorpje::WoorpjeEncoder;

use crate::model::constraints::WordEquation;

use super::ConstraintEncoder;

pub trait WordEquationEncoder: ConstraintEncoder {
    fn new(equation: WordEquation) -> Self;
}
