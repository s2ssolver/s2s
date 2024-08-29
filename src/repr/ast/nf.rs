//! Transforms a script into normal forms, including Boolean normal form (BNF) and negation normal form (NNF).

use std::rc::Rc;

use crate::repr::{
    ast::{AstBuilder, CoreExpr, ExprType, Expression},
    Sort, Sorted,
};

use super::AstError;

/// Transforms an expression into negation normal form.
/// An expression is in negation normal form if negation is only applied to variables.
/// Expression that are not in BNF are first converted to BNF before converting to NNF.
pub fn expression_to_nnf(
    expr: &Rc<Expression>,
    builder: &mut AstBuilder,
) -> Result<Rc<Expression>, AstError> {
    match expr.get_type() {
        ExprType::Core(e) => match e {
            CoreExpr::Var(_) | CoreExpr::Bool(_) => Ok(expr.clone()),
            CoreExpr::Not(inner_e) => match inner_e.get_type() {
                ExprType::Core(inner) => match inner {
                    CoreExpr::Bool(v) => Ok(builder.bool(!v)),
                    CoreExpr::Var(v) => {
                        debug_assert!(v.sort().is_bool());
                        Ok(expr.clone())
                    }
                    CoreExpr::Not(dn) => Ok(dn.clone()),
                    CoreExpr::And(es) => {
                        let new_es = es
                            .iter()
                            .map(|e| expression_to_nnf(&builder.not(e.clone()), builder))
                            .collect::<Result<_, _>>()?;
                        Ok(builder.or(new_es))
                    }
                    CoreExpr::Or(es) => {
                        let new_es = es
                            .iter()
                            .map(|e| expression_to_nnf(&builder.not(e.clone()), builder))
                            .collect::<Result<_, _>>()?;
                        Ok(builder.and(new_es))
                    }
                    CoreExpr::Equal(l, r) => {
                        if !l.sort().is_bool() && !r.sort().is_bool() {
                            Ok(expr.clone())
                        } else {
                            panic!("Can only convert BNF to NNF")
                        }
                    }
                    CoreExpr::Imp(_, _) | CoreExpr::Ite(_, _, _) | CoreExpr::Distinct(_) => {
                        panic!("Can only convert BNF to NNF")
                    }
                },
                _ => Ok(expr.clone()), // all literals are in NNF
            },
            CoreExpr::And(es) => {
                let new_es: Vec<_> = es
                    .iter()
                    .map(|e| expression_to_nnf(e, builder))
                    .collect::<Result<_, _>>()?;
                Ok(builder.and(new_es))
            }
            CoreExpr::Or(es) => {
                let new_es: Vec<_> = es
                    .iter()
                    .map(|e| expression_to_nnf(e, builder))
                    .collect::<Result<_, _>>()?;
                Ok(builder.or(new_es))
            }
            CoreExpr::Equal(l, r) => {
                if !l.sort().is_bool() && !r.sort().is_bool() {
                    Ok(expr.clone())
                } else {
                    let bnf = expression_to_bnf(expr, builder)?;
                    expression_to_nnf(&bnf, builder)
                }
            }
            CoreExpr::Imp(_, _) | CoreExpr::Ite(_, _, _) | CoreExpr::Distinct(_) => {
                let bnf = expression_to_bnf(expr, builder)?;
                expression_to_nnf(&bnf, builder)
            }
        },
        _ => Ok(expr.clone()),
    }
}

/// Transforms an expression into Boolean normal form.
/// An expression is in Boolean normal form if it only uses the operators `and`, `or`, and `not`.
pub fn expression_to_bnf(
    expr: &Rc<Expression>,
    builder: &mut AstBuilder,
) -> Result<Rc<Expression>, AstError> {
    match expr.get_type() {
        ExprType::Core(e) => match e {
            CoreExpr::Var(_) | CoreExpr::Bool(_) => Ok(expr.clone()),
            CoreExpr::Not(e) => {
                let inner = expression_to_bnf(e, builder)?;
                Ok(builder.not(inner))
            }
            CoreExpr::And(es) | CoreExpr::Or(es) => {
                let new_es = es
                    .iter()
                    .map(|e| expression_to_bnf(e, builder))
                    .collect::<Result<_, _>>()?;
                match e {
                    CoreExpr::And(_) => Ok(builder.and(new_es)),
                    CoreExpr::Or(_) => Ok(builder.or(new_es)),
                    _ => unreachable!(),
                }
            }
            CoreExpr::Equal(l, r) if l.sort().is_bool() && r.sort().is_bool() => {
                // Resolve Boolean equivalence as (l -> r) and (r -> l)
                let l2r = builder.imp(l.clone(), r.clone());
                let r2l = builder.imp(r.clone(), l.clone());
                let conj = builder.and(vec![l2r, r2l]);
                expression_to_bnf(&conj, builder)
            }
            CoreExpr::Equal(_, _) => Ok(expr.clone()),
            CoreExpr::Imp(l, r) => {
                // Resolve Boolean implication as (not l or r)
                debug_assert!(l.sort().is_bool() && r.sort().is_bool());
                let not_l = builder.not(l.clone());
                let disj = builder.or(vec![not_l, r.clone()]);
                expression_to_bnf(&disj, builder)
            }
            CoreExpr::Ite(i, _, _) if !i.sort().is_bool() => {
                return Err(AstError::Unsupported(format!(
                    "If condition in ite expressions must be Boolean ({expr})"
                )))
            }
            CoreExpr::Ite(i, t, e) => {
                match (t.sort(), e.sort()) {
                    (Sort::Bool, Sort::Bool) => {
                        // Resolve Boolean ITE as (i ==> t) and (not i ==> e)
                        let i2t = builder.imp(i.clone(), t.clone());
                        let not_i = builder.not(i.clone());
                        let i2e = builder.imp(not_i, e.clone());
                        let conj = builder.and(vec![i2t, i2e]);
                        expression_to_bnf(&conj, builder)
                    }
                    (s1, s2) => {
                        log::error!("BNF for ITE with non-Boolean branches\nTHEN: {t} \t(SORT {s1})\nELSE: {e} \t(SORT {s2})\nIN: {expr}");
                        todo!("BNF for ITE with non-Boolean branches")
                    }
                }
            }
            CoreExpr::Distinct(_) => todo!("BNF for distinct"),
        },
        _ => Ok(expr.clone()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        context::Context,
        repr::{ast::AstBuilder, Sort},
    };

    #[test]
    fn test_bnf_var() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var = builder.var(v);

        // Variable should remain unchanged in BNF
        let bnf = expression_to_bnf(&var, &mut builder).unwrap();
        assert_eq!(var, bnf);
    }

    #[test]
    fn test_nnf_var() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var = builder.var(v);

        // Variable should remain unchanged in NNF
        let nnf = expression_to_nnf(&var, &mut builder).unwrap();
        assert_eq!(var, nnf);
    }

    #[test]
    fn test_bnf_and() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);

        let and_expr = builder.and(vec![var_x.clone(), var_y.clone()]);

        // AND expression should remain unchanged in BNF
        let bnf = expression_to_bnf(&and_expr, &mut builder).unwrap();
        assert_eq!(and_expr, bnf);
    }

    #[test]
    fn test_nnf_and() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);
        let and_expr = builder.and(vec![var_x.clone(), var_y.clone()]);

        // AND expression should remain unchanged in NNF
        let nnf = expression_to_nnf(&and_expr, &mut builder).unwrap();
        assert_eq!(and_expr, nnf);
    }

    #[test]
    fn test_bnf_not() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var = builder.var(v);
        let not_expr = builder.not(var.clone());

        // NOT expression should remain unchanged in BNF
        let bnf = expression_to_bnf(&not_expr, &mut builder).unwrap();
        assert_eq!(not_expr, bnf);
    }

    #[test]
    fn test_nnf_not() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var = builder.var(v);
        let not_expr = builder.not(var.clone());

        // NOT expression should remain unchanged in NNF
        let nnf = expression_to_nnf(&not_expr, &mut builder).unwrap();
        assert_eq!(not_expr, nnf);
    }

    #[test]
    fn test_bnf_or() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);
        let or_expr = builder.or(vec![var_x.clone(), var_y.clone()]);

        // OR expression should remain unchanged in BNF
        let bnf = expression_to_bnf(&or_expr, &mut builder).unwrap();
        assert_eq!(or_expr, bnf);
    }

    #[test]
    fn test_nnf_or() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);
        let or_expr = builder.or(vec![var_x.clone(), var_y.clone()]);

        // OR expression should remain unchanged in NNF
        let nnf = expression_to_nnf(&or_expr, &mut builder).unwrap();
        assert_eq!(or_expr, nnf);
    }

    #[test]
    fn test_bnf_implies() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);
        let implies_expr = builder.imp(var_x.clone(), var_y.clone());

        // Implication (x -> y) should be converted to (not x or y) in BNF
        let bnf = expression_to_bnf(&implies_expr, &mut builder).unwrap();
        let args = vec![builder.not(var_x.clone()), var_y.clone()];
        let expected_bnf = builder.or(args);
        assert_eq!(expected_bnf, bnf);
    }

    #[test]
    fn test_bnf_equivalence() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);
        let eq_expr = builder.eq(var_x.clone(), var_y.clone());

        // Equivalence (x == y) should be converted to (x -> y) and (y -> x) in BNF
        let bnf = expression_to_bnf(&eq_expr, &mut builder).unwrap();
        let not_x = builder.not(var_x.clone());
        let not_y = builder.not(var_y.clone());
        let args = vec![
            builder.or(vec![not_x.clone(), var_y.clone()]),
            builder.or(vec![not_y.clone(), var_x.clone()]),
        ];
        let expected_bnf = builder.and(args);
        assert_eq!(
            expected_bnf, bnf,
            "Expected: {}\nActual: {}",
            expected_bnf, bnf
        );
    }

    #[test]
    fn test_nnf_double_negation() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let v = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var = builder.var(v);

        let neg = builder.not(var.clone());
        let double_neg = builder.not(neg.clone());

        // Double negation should simplify to the original variable
        let nnf = expression_to_nnf(&double_neg, &mut builder).unwrap();
        assert_eq!(var, nnf);
    }

    #[test]
    fn test_nnf_negation_of_and() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);

        let and_expr = builder.and(vec![var_x.clone(), var_y.clone()]);
        let neg_and = builder.not(and_expr);

        // Negation of (x and y) should convert to (not x or not y) in NNF
        let nnf = expression_to_nnf(&neg_and, &mut builder).unwrap();

        let args = vec![builder.not(var_x.clone()), builder.not(var_y.clone())];
        let expected_nnf = builder.or(args);
        assert_eq!(expected_nnf, nnf);
    }

    #[test]
    fn test_nnf_negation_of_or() {
        let mut builder = AstBuilder::default();
        let mut ctx = Context::default();
        let vx = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let var_x = builder.var(vx);
        let vy = ctx.make_var("y".to_string(), Sort::Bool).unwrap();
        let var_y = builder.var(vy);

        let or_expr = builder.or(vec![var_x.clone(), var_y.clone()]);
        let neg_or = builder.not(or_expr);

        // Negation of (x or y) should convert to (not x and not y) in NNF
        let nnf = expression_to_nnf(&neg_or, &mut builder).unwrap();
        let args = vec![builder.not(var_x.clone()), builder.not(var_y.clone())];
        let expected_nnf = builder.and(args);
        assert_eq!(expected_nnf, nnf);
    }
}
