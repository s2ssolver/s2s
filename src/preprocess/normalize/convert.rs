//! Conversion from the AST to the IR.

use std::rc::Rc;

use super::NormalizationError;
use crate::{
    ast::{CoreExpr, ExprType, Expression, Sort, Sorted, StrExpr},
    context::Context,
    ir::{Atom, Formula, FormulaBuilder, Pattern},
};

pub fn convert_expr(
    expr: &Rc<Expression>,
    ctx: &mut Context,
    builder: &mut FormulaBuilder,
) -> Result<Formula, NormalizationError> {
    match expr.get_type() {
        ExprType::Core(CoreExpr::Not(neg)) => match convert_expr(neg, ctx, builder)? {
            Formula::Literal(lit) => {
                // Flip the polarity of the literal
                let flipped = !lit.polarity();
                Ok(builder.literal(lit.into_atom(), flipped))
            }
            Formula::And(_) | Formula::Or(_) => Err(NormalizationError::NotInNNF(expr.to_string())),
        },
        ExprType::Core(CoreExpr::And(es)) => {
            let formulas = es
                .iter()
                .map(|e| convert_expr(e, ctx, builder))
                .collect::<Result<_, _>>()?;
            Ok(builder.and(formulas))
        }
        ExprType::Core(CoreExpr::Or(es)) => {
            let formulas = es
                .iter()
                .map(|e| convert_expr(e, ctx, builder))
                .collect::<Result<_, _>>()?;
            Ok(builder.or(formulas))
        }
        ExprType::Core(_) => Err(NormalizationError::NotInNNF(expr.to_string())),
        ExprType::String(s) => {
            let atom = convert_string_atom(s, builder)?;
            Ok(builder.plit(atom))
        }
        ExprType::Int(_) => todo!(),
    }
}

fn convert_atom(
    expr: &Rc<Expression>,
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    match expr.get_type() {
        ExprType::Core(CoreExpr::Bool(b)) => Ok(builder.bool_const(*b)),
        ExprType::Core(CoreExpr::Var(v)) => Ok(builder.bool_var(v.clone())),
        ExprType::Core(CoreExpr::Equal(lhs, rhs)) => match (lhs.get_type(), rhs.get_type()) {
            (ExprType::String(lhs), ExprType::String(rhs)) => {
                convert_word_equation(lhs, rhs, builder)
            }
            (ExprType::Int(_), ExprType::Int(_)) => todo!(),
            (ExprType::Core(_), ExprType::Core(_)) => {
                Err(NormalizationError::NotInNNF(expr.to_string()))
            }
            _ => Err(NormalizationError::InvalidSort {
                expr: expr.to_string(),
                expected: lhs.sort(),
                got: rhs.sort(),
            }),
        },
        ExprType::Core(_) => Err(NormalizationError::NotInNNF(expr.to_string())),
        ExprType::String(s) => convert_string_atom(s, builder),
        ExprType::Int(_) => todo!(), //convert_int_atom(i, ctx, builder),
    }
}

fn convert_string_atom(
    expr: &StrExpr,
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    match expr {
        StrExpr::InRe(p, r) => match (p.get_type(), r.get_type()) {
            (ExprType::String(p), ExprType::String(r)) => convert_in_re(p, r, builder),
            _ => Err(NormalizationError::Unsupported(expr.to_string())),
        },
        StrExpr::PrefixOf(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_prefix_of(l, r, builder),
            _ => Err(NormalizationError::Unsupported(expr.to_string())),
        },
        StrExpr::SuffixOf(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_suffix_of(l, r, builder),
            _ => Err(NormalizationError::Unsupported(expr.to_string())),
        },
        StrExpr::Contains(l, r) => match (l.get_type(), r.get_type()) {
            (ExprType::String(l), ExprType::String(r)) => convert_contains(l, r, builder),
            _ => Err(NormalizationError::Unsupported(expr.to_string())),
        },
        _ => Err(NormalizationError::Unsupported(expr.to_string())),
    }
}

fn convert_pattern(expr: &StrExpr) -> Option<Pattern> {
    match expr {
        StrExpr::Constant(c) => Some(Pattern::constant(c)),
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
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        None => Err(NormalizationError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        None => Err(NormalizationError::Unsupported(rhs.to_string()))?,
    };
    Ok(builder.word_equation(lhs, rhs))
}

fn convert_in_re(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match rhs {
        StrExpr::Regex(r) => r.clone(),
        _ => Err(NormalizationError::InvalidSort {
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
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
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
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: rhs.to_string(),
            expected: Sort::String,
            got: rhs.sort(),
        })?,
    };
    Ok(builder.suffix_of(lhs, rhs))
}

fn convert_contains(
    lhs: &StrExpr,
    rhs: &StrExpr,
    builder: &mut FormulaBuilder,
) -> Result<Rc<Atom>, NormalizationError> {
    let lhs = match convert_pattern(lhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: lhs.sort(),
        })?,
    };
    let rhs = match convert_pattern(rhs) {
        Some(r) => r,
        _ => Err(NormalizationError::InvalidSort {
            expr: rhs.to_string(),
            expected: Sort::String,
            got: rhs.sort(),
        })?,
    };
    Ok(builder.contains(lhs, rhs))
}
