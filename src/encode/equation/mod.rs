mod alignment;
mod iwoorpje;
mod woorpje;
pub use alignment::AlignmentEncoder;
pub use iwoorpje::IWoorpjeEncoder;
pub use woorpje::WoorpjeEncoder;

use crate::model::words::WordEquation;

use super::PredicateEncoder;

pub trait WordEquationEncoder: PredicateEncoder {
    fn new(equation: WordEquation) -> Self;
}
