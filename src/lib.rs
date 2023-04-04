use std::collections::HashSet;

use formula::Formula;
use model::Variable;

mod encode;
mod formula;
mod model;
mod sat;

pub struct Instance {
    /// The formula to solve
    formula: Formula,
    /// The set of all variables
    vars: HashSet<Variable>,
}
