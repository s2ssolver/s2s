use std::{collections::HashMap, rc::Rc};

use regulaer::re::{OptReBuilder, Regex};

use super::{CoreExpr, ExprType, Expression, IntExpr, StrExpr, Variable};

/// Manages the creation and interning of expressions and variables.
/// All expressions should be created through (the same instance of) this builder.
/// Two syntactically equal expressions created by different builders are not guaranteed to be equal.
/// Thus, it is a logical error to compare expressions created by different builders.
#[derive(Default)]
pub struct AstBuilder {
    next_id: usize,
    fm_registry: HashMap<ExprType, Rc<Expression>>,
    re_buider: OptReBuilder,
}

impl AstBuilder {
    /// Interns an expression, ensuring it is unique.
    fn intern(&mut self, op: ExprType) -> Rc<Expression> {
        if let Some(existing) = self.fm_registry.get(&op) {
            existing.clone()
        } else {
            let fm = Expression::new(self.next_id, op.clone());
            self.next_id += 1;
            let rc = Rc::new(fm.clone());
            self.fm_registry.insert(op, rc.clone());
            rc
        }
    }

    pub fn var(&mut self, v: Rc<Variable>) -> Rc<Expression> {
        let v = ExprType::Core(CoreExpr::Var(v));
        self.intern(v)
    }

    pub fn re_builder(&mut self) -> &mut OptReBuilder {
        &mut self.re_buider
    }

    #[allow(dead_code)]
    pub(crate) fn core_expr(&mut self, expr: CoreExpr) -> Rc<Expression> {
        let e = ExprType::Core(expr);
        self.intern(e)
    }

    pub(crate) fn string_expr(&mut self, expr: StrExpr) -> Rc<Expression> {
        let e = ExprType::String(expr);
        self.intern(e)
    }

    pub(crate) fn int_expr(&mut self, expr: IntExpr) -> Rc<Expression> {
        let e = ExprType::Int(expr);
        self.intern(e)
    }

    pub fn with_args(
        &mut self,
        expression: &Rc<Expression>,
        args: Vec<Rc<Expression>>,
    ) -> Option<Rc<Expression>> {
        match expression.get_type() {
            ExprType::Core(expr) => match expr {
                CoreExpr::Var(_) if args.is_empty() => Some(expression.clone()),
                CoreExpr::Not(_) if args.len() == 1 => Some(self.not(args[0].clone())),
                CoreExpr::And(_) => Some(self.and(args)),
                CoreExpr::Or(_) => Some(self.or(args)),
                CoreExpr::Equal(_, _) if args.len() == 2 => {
                    Some(self.eq(args[0].clone(), args[1].clone()))
                }
                CoreExpr::Imp(_, _) if args.len() == 2 => {
                    Some(self.imp(args[0].clone(), args[1].clone()))
                }
                CoreExpr::Ite(_, _, _) if args.len() == 3 => {
                    Some(self.ite(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                CoreExpr::Distinct(_) => Some(self.distinct(args)),
                _ => None,
            },
            ExprType::String(expr) => match expr {
                StrExpr::Constant(_) if args.is_empty() => Some(expression.clone()),
                StrExpr::Regex(_) if args.is_empty() => Some(expression.clone()),
                StrExpr::Concat(_) => Some(self.concat(args)),
                StrExpr::Length(_) if args.len() == 1 => Some(self.length(args[0].clone())),
                StrExpr::InRe(_, _) if args.len() == 2 => {
                    Some(self.in_re(args[0].clone(), args[1].clone()))
                }
                StrExpr::Substr(_, _, _) if args.len() == 3 => {
                    Some(self.substr(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::PrefixOf(_, _) if args.len() == 2 => {
                    Some(self.prefix_of(args[0].clone(), args[1].clone()))
                }
                StrExpr::SuffixOf(_, _) if args.len() == 2 => {
                    Some(self.suffix_of(args[0].clone(), args[1].clone()))
                }
                StrExpr::Contains(_, _) if args.len() == 2 => {
                    Some(self.contains(args[0].clone(), args[1].clone()))
                }
                StrExpr::IndexOf(_, _, _) if args.len() == 3 => {
                    Some(self.index_of(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::Replace(_, _, _) if args.len() == 3 => {
                    Some(self.replace(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::ReplaceAll(_, _, _) if args.len() == 3 => {
                    Some(self.replace_all(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::ReplaceRe(_, _, _) if args.len() == 3 => {
                    Some(self.replace_re(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::ReplaceReAll(_, _, _) if args.len() == 3 => {
                    Some(self.replace_re_all(args[0].clone(), args[1].clone(), args[2].clone()))
                }
                StrExpr::ToInt(_) if args.len() == 1 => Some(self.to_int(args[0].clone())),
                StrExpr::FromInt(_) if args.len() == 1 => Some(self.from_int(args[0].clone())),
                _ => None,
            },
            ExprType::Int(ext) => match ext {
                IntExpr::Constant(_) if args.is_empty() => Some(expression.clone()),
                IntExpr::Add(_) => Some(self.add(args)),
                IntExpr::Sub(_, _) if args.len() == 2 => {
                    Some(self.sub(args[0].clone(), args[1].clone()))
                }
                IntExpr::Mul(_) => Some(self.mul(args)),
                IntExpr::Div(_, _) if args.len() == 2 => {
                    Some(self.div(args[0].clone(), args[1].clone()))
                }
                IntExpr::Mod(_, _) if args.len() == 2 => {
                    Some(self.mod_(args[0].clone(), args[1].clone()))
                }
                IntExpr::Neg(_) if args.len() == 1 => Some(self.neg(args[0].clone())),
                IntExpr::Abs(_) if args.len() == 1 => Some(self.abs(args[0].clone())),
                IntExpr::Le(_, _) if args.len() == 2 => {
                    Some(self.le(args[0].clone(), args[1].clone()))
                }
                IntExpr::Lt(_, _) if args.len() == 2 => {
                    Some(self.lt(args[0].clone(), args[1].clone()))
                }
                IntExpr::Ge(_, _) if args.len() == 2 => {
                    Some(self.ge(args[0].clone(), args[1].clone()))
                }
                IntExpr::Gt(_, _) if args.len() == 2 => {
                    Some(self.gt(args[0].clone(), args[1].clone()))
                }
                _ => None,
            },
        }
    }

    // pub fn from_pattern(&mut self, p: &Pattern) -> Rc<Expression> {
    //     let mut args = Vec::with_capacity(p.len());
    //     for s in p.iter() {
    //         match s {
    //             Symbol::Const(c) => args.push(self.string(c.clone())),
    //             Symbol::Var(v) => args.push(self.var(v.clone())),
    //         }
    //     }
    //     self.concat(args)
    // }

    /* Core expressions */

    pub fn bool(&mut self, b: bool) -> Rc<Expression> {
        let e = ExprType::Core(CoreExpr::Bool(b));
        self.intern(e)
    }

    pub fn not(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        let e = ExprType::Core(CoreExpr::Not(f));
        self.intern(e)
    }

    pub fn and(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::And(fs)))
    }

    pub fn or(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::Or(fs)))
    }

    pub fn eq(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::Equal(f1, f2)))
    }

    pub fn imp(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::Imp(f1, f2)))
    }

    pub fn distinct(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::Distinct(fs)))
    }

    pub fn ite(
        &mut self,
        i: Rc<Expression>,
        t: Rc<Expression>,
        e: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::Core(CoreExpr::Ite(i, t, e)))
    }

    /* String expressions */

    /// Creates a string constant.
    pub fn string(&mut self, c: String) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Constant(c)))
    }

    pub fn regex(&mut self, r: Regex) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Regex(r)))
    }

    pub fn concat(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Concat(fs)))
    }

    pub fn in_re(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::InRe(f1, f2)))
    }

    pub fn length(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Length(f)))
    }

    pub fn substr(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Substr(f1, f2, f3)))
    }

    pub fn str_at(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::At(f1, f2)))
    }

    pub fn prefix_of(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::PrefixOf(f1, f2)))
    }

    pub fn suffix_of(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::SuffixOf(f1, f2)))
    }

    pub fn contains(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Contains(f1, f2)))
    }

    pub fn index_of(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::IndexOf(f1, f2, f3)))
    }

    pub fn replace(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::Replace(f1, f2, f3)))
    }

    pub fn replace_all(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::ReplaceAll(f1, f2, f3)))
    }

    pub fn replace_re(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::ReplaceRe(f1, f2, f3)))
    }

    pub fn replace_re_all(
        &mut self,
        f1: Rc<Expression>,
        f2: Rc<Expression>,
        f3: Rc<Expression>,
    ) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::ReplaceReAll(f1, f2, f3)))
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn to_int(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::ToInt(f)))
    }

    #[allow(clippy::wrong_self_convention)]
    pub fn from_int(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::String(StrExpr::FromInt(f)))
    }

    /* Integer expressions */

    pub fn int(&mut self, c: isize) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Constant(c)))
    }

    pub fn add(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Add(fs)))
    }

    pub fn sub(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Sub(f1, f2)))
    }

    pub fn mul(&mut self, fs: Vec<Rc<Expression>>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Mul(fs)))
    }

    pub fn div(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Div(f1, f2)))
    }

    pub fn mod_(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Mod(f1, f2)))
    }

    pub fn neg(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Neg(f)))
    }

    pub fn abs(&mut self, f: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Abs(f)))
    }

    pub fn le(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Le(f1, f2)))
    }

    pub fn lt(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Lt(f1, f2)))
    }

    pub fn ge(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Ge(f1, f2)))
    }

    pub fn gt(&mut self, f1: Rc<Expression>, f2: Rc<Expression>) -> Rc<Expression> {
        self.intern(ExprType::Int(IntExpr::Gt(f1, f2)))
    }

    // ...
}

#[cfg(test)]
mod tests {

    use crate::{ast::Sort, context::Context};

    use super::*;

    #[test]
    fn test_var() {
        let mut ctx = Context::default();
        let var = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let mut builder = AstBuilder::default();

        let expr = builder.var(var.clone());
        assert_eq!(*expr.get_type(), ExprType::Core(CoreExpr::Var(var)));
    }

    #[test]
    fn test_not() {
        let mut ctx = Context::default();
        let mut builder = AstBuilder::default();
        let var = ctx.new_var("x".to_string(), Sort::String).unwrap();

        let expr = builder.var(var.clone());
        let not_expr = builder.not(expr.clone());
        assert_eq!(*not_expr.get_type(), ExprType::Core(CoreExpr::Not(expr)));
    }

    #[test]
    fn test_and() {
        let mut ctx = Context::default();
        let mut builder = AstBuilder::default();
        let var1 = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let var2 = ctx.new_var("y".to_string(), Sort::String).unwrap();
        let expr1 = builder.var(var1.clone());
        let expr2 = builder.var(var2.clone());
        let and_expr = builder.and(vec![expr1.clone(), expr2.clone()]);
        assert_eq!(
            *and_expr.get_type(),
            ExprType::Core(CoreExpr::And(vec![expr1, expr2]))
        );
    }

    #[test]
    fn test_or() {
        let mut ctx = Context::default();

        let var1 = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let var2 = ctx.new_var("y".to_string(), Sort::String).unwrap();
        let mut builder = AstBuilder::default();
        let expr1 = builder.var(var1.clone());
        let expr2 = builder.var(var2.clone());
        let or_expr = builder.or(vec![expr1.clone(), expr2.clone()]);
        assert_eq!(
            *or_expr.get_type(),
            ExprType::Core(CoreExpr::Or(vec![expr1, expr2]))
        );
    }

    #[test]
    fn test_equal() {
        let mut ctx = Context::default();
        let var1 = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let var2 = ctx.new_var("y".to_string(), Sort::String).unwrap();

        let mut builder = AstBuilder::default();
        let expr1 = builder.var(var1.clone());
        let expr2 = builder.var(var2.clone());
        let equal_expr = builder.eq(expr1.clone(), expr2.clone());
        assert_eq!(
            *equal_expr.get_type(),
            ExprType::Core(CoreExpr::Equal(expr1, expr2))
        );
    }

    #[test]
    fn test_imp() {
        let mut ctx = Context::default();

        let var1 = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let var2 = ctx.new_var("y".to_string(), Sort::String).unwrap();

        let mut builder = AstBuilder::default();
        let expr1 = builder.var(var1.clone());
        let expr2 = builder.var(var2.clone());
        let imp_expr = builder.imp(expr1.clone(), expr2.clone());
        assert_eq!(
            *imp_expr.get_type(),
            ExprType::Core(CoreExpr::Imp(expr1, expr2))
        );
    }

    #[test]
    fn test_id_equality() {
        let mut ctx = Context::default();

        let var1 = ctx.new_var("x".to_string(), Sort::String).unwrap();
        let var2 = ctx.new_var("y".to_string(), Sort::String).unwrap();

        let var3 = ctx.new_var("z".to_string(), Sort::String).unwrap();
        let mut builder = AstBuilder::default();

        let expr1 = builder.var(var1.clone());
        let expr2 = builder.var(var2.clone());

        // Create two equal expressions
        let equal_expr1 = builder.eq(expr1.clone(), expr2.clone());
        let equal_expr2 = builder.eq(expr1.clone(), expr2.clone());

        // Check that their ids are equal
        assert_eq!(equal_expr1.id(), equal_expr2.id());

        // Create a different expression
        let expr3 = builder.var(var3.clone());
        let different_expr = builder.eq(expr1.clone(), expr3.clone());

        // Check that its id is different
        assert_ne!(equal_expr1.id(), different_expr.id());
    }
}
