//! Conversion from the AST to the IR.

use std::{collections::HashMap, rc::Rc};

use crate::{
    context::Context,
    repr::{
        ast::{nf::expression_to_nnf, CoreExpr, ExprType, Expression, IntExpr, Script, StrExpr},
        ir::{
            Atom, AtomType, Formula, IrBuilder, LinearArithTerm, LinearOperator, LinearSummand,
            Pattern, Symbol,
        },
        Sort, Sorted,
    },
};

use super::PreprocessingError;

/// Converts the script to a formula.
pub fn convert_script(script: &Script, ctx: &mut Context) -> Result<Formula, PreprocessingError> {
    let mut conjuncts = vec![];
    // TODO: Cache the conversion of expressions. AST is interned, so we can use the pointer as a key.
    for expr in script.iter_asserts() {
        let as_nnf = match expression_to_nnf(expr, ctx.ast_builder()) {
            Ok(ok) => ok,
            Err(e) => {
                log::error!("Failed to convert to NNF: {}", e);
                return Err(PreprocessingError::NotInNNF(e.to_string()));
            }
        };

        let fm = convert_expr(&as_nnf, ctx)?;
        conjuncts.push(fm);
    }
    let res = ctx.ir_builder().and(conjuncts);
    Ok(res)
}

/// Converts an AST expression to an IR formula.
pub fn convert_expr(
    expr: &Rc<Expression>,
    ctx: &mut Context,
) -> Result<Formula, PreprocessingError> {
    match expr.get_type() {
        ExprType::Core(CoreExpr::Not(neg)) => match convert_expr(neg, ctx)? {
            Formula::Literal(lit) => {
                if let AtomType::LinearConstraint(lc) = lit.atom().get_type() {
                    // In case of a linear constraint, we simply negate it by flipping the operator
                    let negated = lc.negate();
                    let atom = ctx
                        .ir_builder()
                        .register_atom(AtomType::LinearConstraint(negated));
                    Ok(ctx.ir_builder().plit(atom))
                } else {
                    // Otherwise we flip the polarity of the literal
                    let flipped = !lit.polarity();
                    Ok(ctx.ir_builder().literal(lit.into_atom(), flipped))
                }
            }
            Formula::And(_) | Formula::Or(_) => Err(PreprocessingError::NotInNNF(expr.to_string())),
            Formula::True => Ok(Formula::False),
            Formula::False => Ok(Formula::True),
        },
        ExprType::Core(CoreExpr::Bool(b)) => {
            if *b {
                Ok(Formula::True)
            } else {
                Ok(Formula::False)
            }
        }
        ExprType::Core(CoreExpr::And(es)) => {
            let formulas = es
                .iter()
                .map(|e| convert_expr(e, ctx))
                .collect::<Result<_, _>>()?;
            Ok(ctx.ir_builder().and(formulas))
        }
        ExprType::Core(CoreExpr::Or(es)) => {
            let formulas = es
                .iter()
                .map(|e| convert_expr(e, ctx))
                .collect::<Result<_, _>>()?;
            Ok(ctx.ir_builder().or(formulas))
        }
        ExprType::Core(CoreExpr::Equal(l, r)) => match (l.get_type(), r.get_type()) {
            (ExprType::Core(_), ExprType::Core(_)) => {
                Err(PreprocessingError::NotInNNF(expr.to_string()))
            }
            (ExprType::String(lhs), ExprType::String(rhs)) => {
                let atom = convert_word_equation(lhs, rhs, ctx.ir_builder())?;
                Ok(ctx.ir_builder().plit(atom))
            }
            (_, _) if l.sort().is_int() && r.sort().is_int() => {
                // integer equality
                let l = convert_linear_arith_term(l)?;
                let r = convert_linear_arith_term(r)?;
                let (mut l, r) = normalize_linear(l, r);
                l.canonicalize();
                let atom = ctx.ir_builder().linear_constraint(l, LinearOperator::Eq, r);
                Ok(ctx.ir_builder().plit(atom))
            }
            _ => Err(PreprocessingError::InvalidSort {
                expr: expr.to_string(),
                expected: l.sort(),
                got: r.sort(),
            }),
        },
        ExprType::Core(CoreExpr::Var(x)) => {
            if x.sort().is_bool() {
                let atom = ctx.ir_builder().bool_var(x.clone());
                Ok(ctx.ir_builder().plit(atom))
            } else {
                Err(PreprocessingError::InvalidSort {
                    expr: expr.to_string(),
                    expected: Sort::Bool,
                    got: x.sort(),
                })
            }
        }
        ExprType::Core(_) => Err(PreprocessingError::NotInNNF(expr.to_string())), // TODO: Handle ITE and Distinct
        ExprType::String(s) => {
            let atom = convert_string_atom(s, ctx)?;
            Ok(ctx.ir_builder().plit(atom))
        }
        ExprType::Int(int) => {
            let atom = convert_int_atom(int, ctx);
            Ok(ctx.ir_builder().plit(atom?))
        }
    }
}

fn convert_string_atom(expr: &StrExpr, ctx: &mut Context) -> Result<Rc<Atom>, PreprocessingError> {
    match expr {
        StrExpr::InRe(p, r) => match (p.get_type(), r.get_type()) {
            (ExprType::String(p), ExprType::String(r)) => convert_in_re(p, r, ctx.ir_builder()),
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
        StrExpr::PrefixOf(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_prefix_of(l, r, ctx.ir_builder()),
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
        StrExpr::SuffixOf(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_suffix_of(l, r, ctx.ir_builder()),
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
        StrExpr::Contains(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_contains(l, r, ctx.ir_builder()),
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
        _ => Err(PreprocessingError::Unsupported(expr.to_string())),
    }
}

fn convert_pattern(expr: &StrExpr) -> Option<Pattern> {
    match expr {
        StrExpr::Constant(c) => Some(Pattern::constant(c)),
        StrExpr::Var(v) => {
            if !v.sort().is_string() {
                return None;
            }
            Some(Pattern::variable(v))
        }
        StrExpr::Concat(cs) => {
            let mut pattern = Pattern::empty();
            for c in cs {
                if let ExprType::String(cc) = c.get_type() {
                    pattern.concat(convert_pattern(cc)?);
                } else {
                    return None;
                }
            }
            Some(pattern)
        }
        _ => None,
    }
}

fn convert_word_equation(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut IrBuilder,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        None => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        None => Err(PreprocessingError::Unsupported(rhs.to_string()))?,
    };
    Ok(builder.word_equation(lhs, rhs))
}

fn convert_in_re(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut IrBuilder,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match rhs {
        StrExpr::Regex(r) => r.clone(),
        _ => Err(PreprocessingError::InvalidSort {
            expr: rhs.to_string(),
            expected: Sort::RegLang,
            got: rhs.sort(),
        })?,
    };
    Ok(builder.in_re(lhs, rhs))
}

fn convert_prefix_of(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut IrBuilder,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::InvalidSort {
            expr: rhs.to_string(),
            expected: Sort::String,
            got: rhs.sort(),
        })?,
    };
    Ok(builder.prefix_of(lhs, rhs))
}

fn convert_suffix_of(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut IrBuilder,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    Ok(builder.suffix_of(lhs, rhs))
}

fn convert_contains(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut IrBuilder,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    Ok(builder.contains(lhs, rhs))
}

fn convert_int_atom(expr: &IntExpr, ctx: &mut Context) -> Result<Rc<Atom>, PreprocessingError> {
    match expr {
        IntExpr::Leq(lhs, rhs)
        | IntExpr::Lt(lhs, rhs)
        | IntExpr::Geq(lhs, rhs)
        | IntExpr::Gt(lhs, rhs) => {
            let lhs = convert_linear_arith_term(lhs)?;
            let rhs = convert_linear_arith_term(rhs)?;
            let op = match expr {
                IntExpr::Leq(_, _) => LinearOperator::Leq,
                IntExpr::Lt(_, _) => LinearOperator::Less,
                IntExpr::Geq(_, _) => LinearOperator::Geq,
                IntExpr::Gt(_, _) => LinearOperator::Greater,
                _ => unreachable!(),
            };
            let (mut lhs, rhs) = normalize_linear(lhs, rhs);
            lhs.canonicalize();
            Ok(ctx.ir_builder().linear_constraint(lhs, op, rhs))
        }
        _ => Err(PreprocessingError::Unsupported(expr.to_string())),
    }
}

fn convert_linear_arith_term(expr: &Rc<Expression>) -> Result<LinearArithTerm, PreprocessingError> {
    match expr.get_type() {
        ExprType::String(StrExpr::Length(x)) => {
            if let ExprType::String(inner) = x.get_type() {
                let pat = convert_pattern(inner)
                    .ok_or(PreprocessingError::Unsupported(expr.to_string()))?;
                let term = pattern_to_length(pat)?;
                Ok(term)
                // Make pattern to length
            } else {
                Err(PreprocessingError::InvalidSort {
                    expr: x.to_string(),
                    expected: Sort::String,
                    got: x.sort(),
                })
            }
        }
        ExprType::Int(IntExpr::Constant(c)) => Ok(LinearArithTerm::from_const(*c)),
        ExprType::Int(IntExpr::Var(v)) => Ok(LinearArithTerm::from_var(v.as_ref())),
        ExprType::Int(IntExpr::Add(add)) => {
            let mut term = LinearArithTerm::new();
            for e in add {
                let next = convert_linear_arith_term(e)?;
                term.add(next);
            }
            Ok(term)
        }
        ExprType::Int(IntExpr::Sub(lhs, rhs)) => {
            let mut lhs = convert_linear_arith_term(lhs)?;
            let rhs = convert_linear_arith_term(rhs)?;
            lhs.sub(rhs);
            Ok(lhs)
        }
        ExprType::Int(IntExpr::Mul(lhs)) => {
            let mut res = LinearArithTerm::from_const(1);
            for e in lhs {
                let next = convert_linear_arith_term(e)?;
                res = match LinearArithTerm::multiply(res, next) {
                    Some(r) => r,
                    None => return Err(PreprocessingError::NonLinearArithmetic(expr.to_string())),
                }
            }
            Ok(res)
        }
        _ => Err(PreprocessingError::Unsupported(expr.to_string())),
    }
}

fn pattern_to_length(pat: Pattern) -> Result<LinearArithTerm, PreprocessingError> {
    let mut vars = HashMap::new();
    let mut consts = 0;
    for s in pat.into_iter() {
        match s {
            Symbol::Constant(_) => consts += 1,
            Symbol::Variable(v) => {
                *vars.entry(v).or_default() += 1;
            }
        }
    }
    let mut term = LinearArithTerm::new();
    for (v, c) in vars {
        let summand = LinearSummand::len_variable(v, c);
        term.add_summand(summand);
    }
    term.add_summand(LinearSummand::constant(consts));
    Ok(term)
}

/// Normalizes a linear arithmetic term by moving all constants to the right hand side and all variables to the left hand side.
fn normalize_linear(lhs: LinearArithTerm, rhs: LinearArithTerm) -> (LinearArithTerm, isize) {
    let mut new_lhs = LinearArithTerm::new();
    let mut rhs_const = 0;
    for term in lhs.into_iter() {
        match &term {
            LinearSummand::Const(c) => rhs_const -= c,
            LinearSummand::Mult(_, _) => new_lhs.add_summand(term),
        }
    }
    for term in rhs.into_iter() {
        match &term {
            LinearSummand::Const(c) => rhs_const += c,
            LinearSummand::Mult(_, _) => new_lhs.add_summand(term.flip_sign()),
        }
    }
    (new_lhs, rhs_const)
}

#[cfg(test)]
mod tests {
    use crate::{context::Context, repr::Sort};

    use super::convert_expr;

    #[test]
    fn convert_bool_var() {
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();

        let expr = ctx.ast_builder().var(v.clone());
        let got = convert_expr(&expr, &mut ctx).unwrap();

        let atom = ctx.ir_builder().bool_var(v);
        let lit = ctx.ir_builder().plit(atom);
        assert_eq!(got, lit);
    }

    #[test]
    fn convert_int_var_to_bool_var() {
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Int).unwrap();

        let expr = ctx.ast_builder().var(v.clone());
        let got = convert_expr(&expr, &mut ctx);
        assert!(got.is_err())
    }
}
