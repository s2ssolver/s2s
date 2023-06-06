use super::Variable;

pub enum LinearType {
    Eq,
    Leq,
}

/// A linear constraint
pub struct LinearConstraint {
    pub lhs: Vec<(Variable, i64)>,
    pub rhs: i64,
    pub typ: LinearType,
}
