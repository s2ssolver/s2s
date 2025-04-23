mod eq;
mod ineq;
mod matching;
mod word;

pub use eq::WordEquationEncoder;
pub use ineq::WordInEquationEncoder;

#[cfg(test)]
mod testutils {
    use crate::ast::canonical::{self, WordEquation};
    use crate::ast::{self, NodeKind};
    use crate::context::Context;
    use crate::preprocess;

    pub(crate) fn parse_simple_equation(lhs: &str, rhs: &str, ctx: &mut Context) -> WordEquation {
        ctx.ast().set_optimize(false);
        let node = ast::testutils::parse_equation(lhs, rhs, ctx);
        let c = preprocess::canonicalize(&node, ctx);
        match c.kind() {
            NodeKind::Literal(literal) => match literal.atom().kind() {
                canonical::AtomKind::WordEquation(weq) => weq.clone(),
                _ => unreachable!(),
            },
            x => unreachable!("Expected a literal but got {x}"),
        }
    }
}
