mod eq;
mod ineq;
mod matching;
mod word;

pub use eq::WordEquationEncoder;
pub use ineq::WordInEquationEncoder;

#[cfg(test)]
mod testutils {
    use crate::ast::{self, NodeKind};
    use crate::ast::{
        canonical::{self, WordEquation},
        NodeManager,
    };
    use crate::preprocess;

    pub(crate) fn parse_simple_equation(
        lhs: &str,
        rhs: &str,
        mngr: &mut NodeManager,
    ) -> WordEquation {
        mngr.set_optimize(false);
        let node = ast::testutils::parse_equation(lhs, rhs, mngr);
        let c = preprocess::canonicalize(&node, mngr);
        match c.kind() {
            NodeKind::Literal(literal) => match literal.atom().kind() {
                canonical::AtomKind::WordEquation(weq) => weq.clone(),
                _ => unreachable!(),
            },
            x => unreachable!("Expected a literal but got {x}"),
        }
    }
}
