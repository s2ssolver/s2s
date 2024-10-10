//! Transforms a script into normal forms, including Boolean normal form (BNF) and negation normal form (NNF).

use crate::smt::{CoreExpr, Expression};

use super::{AstError, AstNode, Sort};

/// Transforms an expression into negation normal form.
/// An expression is in negation normal form if negation is only applied to variables.
/// Expression that are not in BNF are first converted to BNF before converting to NNF.
pub fn expression_into_nnf(expr: Expression) -> Result<Expression, AstError> {
    match expr {
        Expression::Core(e) => match *e {
            CoreExpr::Var(v) => Ok(Expression::Core(Box::new(CoreExpr::Var(v)))),
            CoreExpr::Bool(v) => Ok(Expression::Core(Box::new(CoreExpr::Bool(v)))),
            CoreExpr::Not(negated) => match negated {
                Expression::Core(inner) => match *inner {
                    CoreExpr::Bool(v) => Ok(CoreExpr::Bool(!v).into()),
                    CoreExpr::Var(v) => {
                        let v = CoreExpr::Var(v.clone()).into();
                        Ok(CoreExpr::Not(v).into())
                    }
                    CoreExpr::Not(dn) => Ok(dn.clone()), // double negation
                    CoreExpr::And(es) => {
                        let new_es = es
                            .iter()
                            .map(|e| expression_into_nnf(CoreExpr::Not(e.clone()).into()))
                            .collect::<Result<_, _>>()?;
                        Ok(CoreExpr::Or(new_es).into())
                    }
                    CoreExpr::Or(es) => {
                        let new_es = es
                            .into_iter()
                            .map(|e| expression_into_nnf(CoreExpr::Not(e.clone()).into()))
                            .collect::<Result<_, _>>()?;
                        Ok(CoreExpr::And(new_es).into())
                    }
                    CoreExpr::Equal(l, r) => {
                        if !l.sort().is_bool() && !r.sort().is_bool() {
                            Ok(CoreExpr::Not(CoreExpr::Equal(l, r).into()).into())
                        } else {
                            let bnf = expression_to_bnf(
                                CoreExpr::Not(CoreExpr::Equal(l, r).into()).into(),
                            )?;
                            expression_into_nnf(bnf)
                        }
                    }
                    CoreExpr::Imp(l, r) => {
                        let bnf =
                            expression_to_bnf(CoreExpr::Not(CoreExpr::Imp(l, r).into()).into())?;
                        expression_into_nnf(bnf)
                    }
                    CoreExpr::Ite(i, t, e) => {
                        let bnf =
                            expression_to_bnf(CoreExpr::Not(CoreExpr::Ite(i, t, e).into()).into())?;
                        expression_into_nnf(bnf)
                    }
                    CoreExpr::Distinct(rs) => {
                        let bnf =
                            expression_to_bnf(CoreExpr::Not(CoreExpr::Distinct(rs).into()).into())?;
                        expression_into_nnf(bnf)
                    }
                },
                Expression::String(str_expr) => {
                    Ok(CoreExpr::Not(Expression::String(str_expr)).into())
                }
                Expression::Int(int_expr) => Ok(CoreExpr::Not(Expression::Int(int_expr)).into()),
            },
            CoreExpr::And(es) => {
                let new_es: Vec<_> = es
                    .into_iter()
                    .map(|e| expression_into_nnf(e))
                    .collect::<Result<_, _>>()?;
                Ok(CoreExpr::And(new_es).into())
            }
            CoreExpr::Or(es) => {
                let new_es: Vec<_> = es
                    .into_iter()
                    .map(|e| expression_into_nnf(e))
                    .collect::<Result<_, _>>()?;
                Ok(CoreExpr::Or(new_es).into())
            }
            CoreExpr::Equal(l, r) => {
                if !l.sort().is_bool() && !r.sort().is_bool() {
                    Ok(CoreExpr::Equal(l, r).into())
                } else {
                    let bnf = expression_to_bnf(CoreExpr::Equal(l, r).into())?;
                    expression_into_nnf(bnf)
                }
            }
            CoreExpr::Imp(l, r) => {
                let bnf = expression_to_bnf(CoreExpr::Imp(l, r).into())?;
                expression_into_nnf(bnf)
            }
            CoreExpr::Ite(i, t, e) => {
                let bnf = expression_to_bnf(CoreExpr::Ite(i, t, e).into())?;
                expression_into_nnf(bnf)
            }
            CoreExpr::Distinct(rs) => {
                let bnf = expression_to_bnf(CoreExpr::Distinct(rs).into())?;
                expression_into_nnf(bnf)
            }
        },
        _ => Ok(expr.clone()),
    }
}

/// Transforms an expression into Boolean normal form.
/// An expression is in Boolean normal form if it only uses the operators `and`, `or`, and `not`.
pub fn expression_to_bnf(expr: Expression) -> Result<Expression, AstError> {
    match expr {
        Expression::Core(e) => match *e {
            CoreExpr::Var(v) => Ok(CoreExpr::Var(v).into()),
            CoreExpr::Bool(v) => Ok(CoreExpr::Bool(v).into()),
            CoreExpr::Not(e) => {
                let inner = expression_to_bnf(e)?;
                Ok(CoreExpr::Not(inner).into())
            }
            CoreExpr::And(es) => {
                let new_es = es
                    .into_iter()
                    .map(|e| expression_to_bnf(e))
                    .collect::<Result<_, _>>()?;

                Ok(CoreExpr::And(new_es).into())
            }
            CoreExpr::Or(es) => {
                let new_es = es
                    .into_iter()
                    .map(|e| expression_to_bnf(e))
                    .collect::<Result<_, _>>()?;

                Ok(CoreExpr::Or(new_es).into())
            }
            CoreExpr::Equal(l, r) if l.sort().is_bool() && r.sort().is_bool() => {
                // Resolve Boolean equivalence as (l -> r) and (r -> l)
                let l2r = CoreExpr::Imp(l.clone(), r.clone()).into();
                let r2l = CoreExpr::Imp(r.clone(), l.clone()).into();
                let conj = CoreExpr::And(vec![l2r, r2l]).into();
                expression_to_bnf(conj)
            }
            CoreExpr::Equal(l, r) => Ok(CoreExpr::Equal(l, r).into()),
            CoreExpr::Imp(l, r) => {
                // Resolve Boolean implication as (not l or r)
                debug_assert!(l.sort().is_bool() && r.sort().is_bool());
                let not_l = CoreExpr::Not(l.clone()).into();
                let disj = CoreExpr::Or(vec![not_l, r.clone()]).into();
                expression_to_bnf(disj)
            }
            CoreExpr::Ite(i, _, _) if !i.sort().is_bool() => {
                return Err(AstError::Unsupported(format!(
                    "If condition in ite expressions must be Boolean ({i})"
                )))
            }
            CoreExpr::Ite(i, t, e) => {
                match (t.sort(), e.sort()) {
                    (Sort::Bool, Sort::Bool) => {
                        // Resolve Boolean ITE as (i ==> t) and (not i ==> e)
                        let i2t = CoreExpr::Imp(i.clone(), t.clone()).into();
                        let not_i = CoreExpr::Not(i.clone()).into();
                        let i2e = CoreExpr::Imp(not_i, e.clone()).into();
                        let conj = CoreExpr::And(vec![i2t, i2e]).into();
                        expression_to_bnf(conj)
                    }
                    (s1, s2) => {
                        log::error!("BNF for ITE with non-Boolean branches\nTHEN: {t} \t(SORT {s1})\nELSE: {e} \t(SORT {s2})");
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

    #[test]
    fn test_bnf_var() {
        let var: Expression = CoreExpr::Var("v".into()).into();

        // Variable should remain unchanged in BNF
        let bnf = expression_to_bnf(var.clone()).unwrap();
        assert_eq!(var, bnf);
    }

    #[test]
    fn test_nnf_var() {
        let var: Expression = CoreExpr::Var("v".into()).into();

        // Variable should remain unchanged in NNF
        let nnf = expression_into_nnf(var.clone()).unwrap();
        assert_eq!(var, nnf);
    }

    #[test]
    fn test_bnf_and() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let and_expr: Expression = CoreExpr::And(vec![var_x.clone(), var_y.clone()]).into();

        // AND expression should remain unchanged in BNF
        let bnf = expression_to_bnf(and_expr.clone()).unwrap();
        assert_eq!(and_expr, bnf);
    }

    #[test]
    fn test_nnf_and() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let and_expr: Expression = CoreExpr::And(vec![var_x.clone(), var_y.clone()]).into();

        // AND expression should remain unchanged in NNF
        let nnf = expression_into_nnf(and_expr.clone()).unwrap();
        assert_eq!(and_expr, nnf);
    }

    #[test]
    fn test_bnf_not() {
        let var = CoreExpr::Var("x".into()).into();
        let not_expr: Expression = CoreExpr::Not(var).into();

        // NOT expression should remain unchanged in BNF
        let bnf = expression_to_bnf(not_expr.clone()).unwrap();
        assert_eq!(not_expr, bnf);
    }

    #[test]
    fn test_nnf_not() {
        let var = CoreExpr::Var("x".into()).into();
        let not_expr: Expression = CoreExpr::Not(var).into();

        // NOT expression should remain unchanged in NNF
        let nnf = expression_into_nnf(not_expr.clone()).unwrap();
        assert_eq!(not_expr, nnf);
    }

    #[test]
    fn test_bnf_or() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let or_expr: Expression = CoreExpr::Or(vec![var_x.clone(), var_y.clone()]).into();

        // OR expression should remain unchanged in BNF
        let bnf = expression_to_bnf(or_expr.clone()).unwrap();
        assert_eq!(or_expr, bnf);
    }

    #[test]
    fn test_nnf_or() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let or_expr: Expression = CoreExpr::Or(vec![var_x.clone(), var_y.clone()]).into();

        // OR expression should remain unchanged in NNF
        let nnf = expression_into_nnf(or_expr.clone()).unwrap();
        assert_eq!(or_expr, nnf);
    }

    #[test]
    fn test_bnf_implies() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();

        let var_y: Expression = CoreExpr::Var("y".into()).into();
        let implies_expr: Expression = CoreExpr::Imp(var_x.clone(), var_y.clone()).into();

        // Implication (x -> y) should be converted to (not x or y) in BNF
        let bnf = expression_to_bnf(implies_expr).unwrap();
        let expected_bnf: Expression =
            CoreExpr::Or(vec![CoreExpr::Not(var_x).into(), var_y]).into();
        assert_eq!(expected_bnf, bnf);
    }

    #[test]
    fn test_bnf_equivalence() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();

        let var_y: Expression = CoreExpr::Var("y".into()).into();
        let eq_expr = CoreExpr::Equal(var_x.clone(), var_y.clone()).into();

        // Equivalence (x == y) should be converted to (x -> y) and (y -> x) in BNF
        let bnf = expression_to_bnf(eq_expr).unwrap();

        let not_x: Expression = CoreExpr::Not(var_x.clone()).into();
        let not_y: Expression = CoreExpr::Not(var_y.clone()).into();
        let expected_bnf: Expression = CoreExpr::And(vec![
            CoreExpr::Or(vec![not_x.clone(), var_y.clone()]).into(),
            CoreExpr::Or(vec![not_y.clone(), var_x.clone()]).into(),
        ])
        .into();
        assert_eq!(
            expected_bnf, bnf,
            "Expected: {}\nActual: {}",
            expected_bnf, bnf
        );
    }

    #[test]
    fn test_nnf_double_negation() {
        let var: Expression = CoreExpr::Var("x".into()).into();

        let neg = CoreExpr::Not(var.clone()).into();
        let double_neg = CoreExpr::Not(neg).into();

        // Double negation should simplify to the original variable
        let nnf = expression_into_nnf(double_neg).unwrap();
        assert_eq!(var, nnf);
    }

    #[test]
    fn test_nnf_negation_of_and() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let and_expr: Expression = CoreExpr::And(vec![var_x.clone(), var_y.clone()]).into();
        let neg_and = CoreExpr::Not(and_expr).into();

        // Negation of (x and y) should convert to (not x or not y) in NNF
        let nnf = expression_into_nnf(neg_and).unwrap();

        let expected_nnf: Expression = CoreExpr::Or(vec![
            CoreExpr::Not(var_x.clone()).into(),
            CoreExpr::Not(var_y.clone()).into(),
        ])
        .into();
        assert_eq!(expected_nnf, nnf);
    }

    #[test]
    fn test_nnf_negation_of_or() {
        let var_x: Expression = CoreExpr::Var("x".into()).into();
        let var_y: Expression = CoreExpr::Var("y".into()).into();

        let or_expr: Expression = CoreExpr::Or(vec![var_x.clone(), var_y.clone()]).into();
        let neg_or = CoreExpr::Not(or_expr).into();

        // Negation of (x or y) should convert to (not x and not y) in NNF
        let nnf = expression_into_nnf(neg_or).unwrap();
        let expected_nnf: Expression = CoreExpr::And(vec![
            CoreExpr::Not(var_x.clone()).into(),
            CoreExpr::Not(var_y.clone()).into(),
        ])
        .into();
        assert_eq!(expected_nnf, nnf);
    }
}
