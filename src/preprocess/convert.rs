//! Conversion from the AST to the IR.

use std::{collections::HashMap, rc::Rc};

use regulaer::re::Regex;

use crate::{
    context::{Context, Sort, Sorted},
    ir::{
        Atom, AtomType, Formula, LinearArithTerm, LinearOperator, LinearSummand, Pattern, Symbol,
    },
    smt::{
        nf::expression_into_nnf, AstNode, CoreExpr, Expression, IntExpr, Script, SmtCommand,
        Sort as SmtSort, StrExpr,
    },
};

use super::PreprocessingError;

/// Converts the script to a formula.
pub fn convert_script(script: &Script, ctx: &mut Context) -> Result<Formula, PreprocessingError> {
    let mut conjuncts = vec![];

    for (symbol, sort) in script.declared_vars() {
        let sort = convert_sort(*sort);
        if ctx.make_var(symbol.clone(), sort).is_none() {
            return Err(PreprocessingError::AlreadyDeclared(symbol.clone()));
        }
    }

    for assert in script.iter() {
        if let SmtCommand::Assert(a) = assert {
            let as_nnf = match expression_into_nnf(a.clone()) {
                Ok(ok) => ok,
                Err(e) => {
                    log::error!("Failed to convert to NNF: {}", e);
                    return Err(PreprocessingError::NotInNNF(e.to_string()));
                }
            };

            let fm = convert_expr(&as_nnf, ctx)?;
            conjuncts.push(fm);
        }
    }
    let res = ctx.ir_builder().and(conjuncts);
    Ok(res)
}

pub fn convert_sort(sort: SmtSort) -> Sort {
    match sort {
        SmtSort::Bool => Sort::Bool,
        SmtSort::Int => Sort::Int,
        SmtSort::String => Sort::String,
        SmtSort::RegLan => Sort::RegLan,
    }
}

/// Converts an AST expression to an IR formula.
pub fn convert_expr(expr: &Expression, ctx: &mut Context) -> Result<Formula, PreprocessingError> {
    match expr {
        Expression::Core(c) => match c.as_ref() {
            CoreExpr::Not(neg) => match convert_expr(neg, ctx)? {
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
                Formula::And(_) | Formula::Or(_) => {
                    Err(PreprocessingError::NotInNNF(expr.to_string()))
                }
                Formula::True => Ok(Formula::False),
                Formula::False => Ok(Formula::True),
            },
            CoreExpr::Bool(b) => {
                if *b {
                    Ok(Formula::True)
                } else {
                    Ok(Formula::False)
                }
            }
            CoreExpr::And(es) => {
                let formulas = es
                    .into_iter()
                    .map(|e| convert_expr(e, ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.ir_builder().and(formulas))
            }
            CoreExpr::Or(es) => {
                let formulas = es
                    .into_iter()
                    .map(|e| convert_expr(e, ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.ir_builder().or(formulas))
            }
            CoreExpr::Equal(l, r) => match (l, r) {
                (Expression::Core(_), Expression::Core(_)) => {
                    Err(PreprocessingError::NotInNNF(expr.to_string()))
                }
                (Expression::String(_), Expression::String(_)) => {
                    let atom = convert_word_equation(l, r, ctx)?;
                    Ok(ctx.ir_builder().plit(atom))
                }
                (_, _) if l.sort().is_int() && r.sort().is_int() => {
                    // integer equality
                    let l = convert_linear_arith_term(l, ctx)?;
                    let r = convert_linear_arith_term(r, ctx)?;
                    let (mut l, r) = normalize_linear(l, r);
                    l.canonicalize();
                    let atom = ctx.ir_builder().linear_constraint(l, LinearOperator::Eq, r);
                    Ok(ctx.ir_builder().plit(atom))
                }
                _ => Err(PreprocessingError::InvalidSort {
                    expr: expr.to_string(),
                    expected: convert_sort(l.sort()),
                    got: convert_sort(r.sort()),
                }),
            },
            CoreExpr::Var(x) => {
                if let Some(v) = ctx.get_var(&x) {
                    let atom = ctx.ir_builder().bool_var(v.clone());
                    Ok(ctx.ir_builder().plit(atom))
                } else {
                    Err(PreprocessingError::UndeclaredVariable(x.to_string()))
                }
            }
            _ => Err(PreprocessingError::NotInNNF(expr.to_string())), // TODO: Handle ITE and Distinct
        },

        Expression::String(s) => {
            let atom = convert_string_atom(s, ctx)?;
            Ok(ctx.ir_builder().plit(atom))
        }
        Expression::Int(int) => {
            let atom = convert_int_atom(int, ctx);
            Ok(ctx.ir_builder().plit(atom?))
        }
    }
}

fn convert_string_atom(expr: &StrExpr, ctx: &mut Context) -> Result<Rc<Atom>, PreprocessingError> {
    match expr {
        StrExpr::InRe(p, r) => convert_in_re(p, r, ctx),
        StrExpr::PrefixOf(l, r) => convert_prefix_of(l, r, ctx),
        StrExpr::SuffixOf(l, r) => convert_suffix_of(l, r, ctx),
        StrExpr::Contains(l, r) => convert_contains(l, r, ctx),
        _ => Err(PreprocessingError::Unsupported(expr.to_string())),
    }
}

fn convert_pattern(expr: &Expression, ctx: &mut Context) -> Option<Pattern> {
    match expr {
        Expression::String(s) => match s.as_ref() {
            StrExpr::Constant(c) => Some(Pattern::constant(&c)),
            StrExpr::Var(v) => {
                let v = if let Some(v) = ctx.get_var(&v) {
                    v
                } else {
                    return None;
                };
                if !v.sort().is_string() {
                    return None;
                }
                Some(Pattern::variable(&v))
            }
            StrExpr::Concat(cs) => {
                let mut pattern = Pattern::empty();
                for c in cs {
                    pattern.concat(convert_pattern(c, ctx)?);
                }
                Some(pattern)
            }
            _ => None,
        },
        _ => None,
    }
}

fn convert_word_equation(
    lhs: &Expression,
    rhs: &Expression,
    ctx: &mut Context,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs, ctx) {
        Some(r) => r,
        None => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs, ctx) {
        Some(r) => r,
        None => Err(PreprocessingError::Unsupported(rhs.to_string()))?,
    };
    Ok(ctx.ir_builder().word_equation(lhs, rhs))
}

fn convert_in_re(
    lhs: &Expression,
    rhs: &Expression,
    ctx: &mut Context,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::InvalidSort {
            expr: lhs.to_string(),
            expected: Sort::String,
            got: convert_sort(lhs.sort()),
        })?,
    };
    let rhs = convert_regex(rhs, ctx)?;
    Ok(ctx.ir_builder().in_re(lhs, rhs))
}

fn convert_regex(re: &Expression, ctx: &mut Context) -> Result<Regex, PreprocessingError> {
    match re {
        Expression::String(re) => match re.as_ref() {
            StrExpr::ReAll => Ok(ctx.re_builder().all()),
            StrExpr::ReNone => Ok(ctx.re_builder().none()),
            StrExpr::ReAllChar => Ok(ctx.re_builder().any_char()),
            StrExpr::ToRe(str) => match str {
                Expression::String(str_expr) => match str_expr.as_ref() {
                    StrExpr::Constant(w) => Ok(ctx.re_builder().word(w.clone().into())),
                    _ => Err(PreprocessingError::Unsupported(re.to_string())),
                },
                _ => Err(PreprocessingError::Unsupported(re.to_string())),
            },
            StrExpr::ReRange(l, u) => {
                let l = match l {
                    Expression::String(ll) => match ll.as_ref() {
                        StrExpr::Constant(str) => {
                            if str.len() == 1 {
                                str.chars().next().unwrap()
                            } else {
                                return Ok(ctx.re_builder().none());
                            }
                        }
                        _ => return Err(PreprocessingError::Unsupported(re.to_string())),
                    },
                    _ => return Err(PreprocessingError::Unsupported(re.to_string())),
                };
                let u = match u {
                    Expression::String(uu) => match uu.as_ref() {
                        StrExpr::Constant(str) => {
                            if str.len() == 1 {
                                str.chars().next().unwrap()
                            } else {
                                return Ok(ctx.re_builder().none());
                            }
                        }
                        _ => return Err(PreprocessingError::Unsupported(re.to_string())),
                    },
                    _ => return Err(PreprocessingError::Unsupported(re.to_string())),
                };
                Ok(ctx.re_builder().range(l, u))
            }
            StrExpr::ReConcat(rs) => {
                let converted = rs
                    .into_iter()
                    .map(|r| convert_regex(r, ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.re_builder().concat(converted))
            }
            StrExpr::ReUnion(rs) => {
                let converted = rs
                    .into_iter()
                    .map(|r| convert_regex(r, ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.re_builder().union(converted))
            }
            StrExpr::ReInter(rs) => {
                let converted = rs
                    .into_iter()
                    .map(|r| convert_regex(r, ctx))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.re_builder().inter(converted))
            }
            StrExpr::ReStar(r) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().star(converted))
            }
            StrExpr::RePlus(r) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().plus(converted))
            }
            StrExpr::ReOpt(r) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().opt(converted))
            }
            StrExpr::ReComp(r) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().comp(converted))
            }
            StrExpr::ReDiff(r, r1) => {
                let converted = convert_regex(r, ctx)?;
                let converted1 = convert_regex(r1, ctx)?;
                Ok(ctx.re_builder().diff(converted, converted1))
            }
            StrExpr::RePow(r, e) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().pow(converted, *e))
            }
            StrExpr::ReLoop(r, l, u) => {
                let converted = convert_regex(r, ctx)?;
                Ok(ctx.re_builder().loop_(converted, *l, *u))
            }
            _ => Err(PreprocessingError::Unsupported(re.to_string())),
        },
        _ => Err(PreprocessingError::Unsupported(re.to_string())),
    }
}

fn convert_prefix_of(
    lhs: &Expression,
    rhs: &Expression,
    ctx: &mut Context,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(rhs.to_string()))?,
    };
    Ok(ctx.ir_builder().prefix_of(lhs, rhs))
}

fn convert_suffix_of(
    lhs: &Expression,
    rhs: &Expression,
    ctx: &mut Context,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    Ok(ctx.ir_builder().suffix_of(lhs, rhs))
}

fn convert_contains(
    lhs: &Expression,
    rhs: &Expression,
    ctx: &mut Context,
) -> Result<Rc<Atom>, PreprocessingError> {
    let lhs = match convert_pattern(lhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    let rhs = match convert_pattern(rhs, ctx) {
        Some(r) => r,
        _ => Err(PreprocessingError::Unsupported(lhs.to_string()))?,
    };
    Ok(ctx.ir_builder().contains(lhs, rhs))
}

fn convert_int_atom(expr: &IntExpr, ctx: &mut Context) -> Result<Rc<Atom>, PreprocessingError> {
    match expr {
        IntExpr::Leq(lhs, rhs)
        | IntExpr::Lt(lhs, rhs)
        | IntExpr::Geq(lhs, rhs)
        | IntExpr::Gt(lhs, rhs) => {
            let lhs = convert_linear_arith_term(lhs, ctx)?;
            let rhs = convert_linear_arith_term(rhs, ctx)?;
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

fn convert_linear_arith_term(
    expr: &Expression,
    ctx: &mut Context,
) -> Result<LinearArithTerm, PreprocessingError> {
    match expr {
        Expression::String(str_expr) => match str_expr.as_ref() {
            StrExpr::Length(x) => {
                let pat = convert_pattern(x, ctx)
                    .ok_or(PreprocessingError::Unsupported(expr.to_string()))?;
                let term = pattern_to_length(pat)?;
                Ok(term)
            }
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
        Expression::Int(int_expr) => match int_expr.as_ref() {
            IntExpr::Constant(c) => Ok(LinearArithTerm::from_const(*c)),
            IntExpr::Var(v) => match ctx.get_var(&v) {
                Some(v) => {
                    if v.sort().is_int() {
                        Ok(LinearArithTerm::from_var(&v))
                    } else {
                        Err(PreprocessingError::InvalidSort {
                            expr: v.to_string(),
                            expected: Sort::Int,
                            got: v.sort(),
                        })
                    }
                }
                None => Err(PreprocessingError::UndeclaredVariable(v.to_string())),
            },
            IntExpr::Add(add) => {
                let mut term = LinearArithTerm::new();
                for e in add {
                    let next = convert_linear_arith_term(e, ctx)?;
                    term.add(next);
                }
                Ok(term)
            }
            IntExpr::Sub(lhs, rhs) => {
                let mut lhs = convert_linear_arith_term(lhs, ctx)?;
                let rhs = convert_linear_arith_term(rhs, ctx)?;
                lhs.sub(rhs);
                Ok(lhs)
            }
            IntExpr::Mul(lhs) => {
                let mut res = LinearArithTerm::from_const(1);
                for e in lhs {
                    let next = convert_linear_arith_term(e, ctx)?;
                    res = match LinearArithTerm::multiply(res, next) {
                        Some(r) => r,
                        None => {
                            return Err(PreprocessingError::NonLinearArithmetic(expr.to_string()))
                        }
                    }
                }
                Ok(res)
            }
            _ => Err(PreprocessingError::Unsupported(expr.to_string())),
        },
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

    use crate::{
        context::{Context, Sort},
        smt::{CoreExpr, IntExpr},
    };

    use super::convert_expr;

    #[test]
    fn convert_bool_var() {
        let mut ctx = Context::default();
        ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let v = CoreExpr::Var("x".into());

        let got = convert_expr(&v.clone().into(), &mut ctx).unwrap();

        let vv = ctx.make_var("x".into(), Sort::Bool).unwrap();
        let atom = ctx.ir_builder().bool_var(vv);
        let lit = ctx.ir_builder().plit(atom);
        assert_eq!(got, lit);
    }

    #[test]
    fn convert_int_var_to_bool_var() {
        let mut ctx = Context::default();
        let v = IntExpr::Var("x".into());

        let got = convert_expr(&v.into(), &mut ctx);
        assert!(got.is_err())
    }
}
