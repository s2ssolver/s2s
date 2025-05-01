mod eq;
mod ineq;
mod matching;
mod word;

pub use eq::WordEquationEncoder;
pub use ineq::WordInEquationEncoder;

#[cfg(test)]
mod testutils {
    use smt_str::SmtString;

    use crate::ast::{self, VarSubstitution};
    use crate::context::Context;
    use crate::ir::{Atom, Pattern};
    use crate::ir::{Symbol, WordEquation};

    pub(crate) fn parse_simple_equation(lhs: &str, rhs: &str, ctx: &mut Context) -> WordEquation {
        ctx.ast().set_simplify(false);
        let node = ast::testutils::parse_equation(lhs, rhs, ctx);
        if let Atom::WordEquation(weq) = ctx.to_ir(&node).unwrap().atom().as_ref() {
            weq.clone()
        } else {
            unreachable!()
        }
    }

    fn apply_sub(p: &Pattern, sol: &VarSubstitution) -> Option<SmtString> {
        let mut res = SmtString::empty();
        for s in p.symbols() {
            match s {
                Symbol::Constant(c) => res.push(*c),
                Symbol::Variable(v) => {
                    let sub = sol.get(v)?.as_str_const()?;
                    res.append(&sub);
                }
            }
        }
        Some(res)
    }

    pub(crate) fn is_solution(eq: &WordEquation, sol: &VarSubstitution) -> bool {
        let lhs_const = apply_sub(&eq.lhs(), sol);
        let rhs_const = apply_sub(&eq.rhs(), sol);
        match (lhs_const, rhs_const) {
            (Some(l), Some(r)) => l == r,
            _ => false,
        }
    }
}
