mod eq;
mod ineq;
mod matching;
mod word;

pub use eq::WordEquationEncoder;
pub use ineq::WordInEquationEncoder;

#[cfg(test)]
mod testutils {
    use crate::node;
    use crate::{
        canonical::{self, WordEquation},
        node::NodeManager,
    };

    pub(crate) fn parse_simple_equation(
        lhs: &str,
        rhs: &str,
        mngr: &mut NodeManager,
    ) -> WordEquation {
        let node = node::testutils::parse_equation(lhs, rhs, mngr);
        let c = canonical::canonicalize(&node, mngr).unwrap();
        match c.kind() {
            canonical::FormulaKind::Literal(literal) => match literal.atom().kind() {
                canonical::AtomKind::WordEquation(weq) => weq.clone(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}
