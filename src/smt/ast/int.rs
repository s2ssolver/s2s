use std::fmt::Display;

use crate::smt::{Sort, Symbol};

use super::{AstNode, Expression};

/// The SMT-LIB integer expressions.
/// Note that these comprise the operations defined in the SMT-LIB theory of integers (QF_*IA).
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum IntExpr {
    Constant(isize),
    Var(Symbol),
    Add(Vec<Expression>),
    Sub(Expression, Expression),
    Mul(Vec<Expression>),
    Div(Expression, Expression),
    Mod(Expression, Expression),
    Neg(Expression),
    Abs(Expression),
    Leq(Expression, Expression),
    Lt(Expression, Expression),
    Geq(Expression, Expression),
    Gt(Expression, Expression),
}

impl AstNode for IntExpr {
    fn children(&self) -> Vec<&Expression> {
        match self {
            IntExpr::Var(_) | IntExpr::Constant(_) => vec![],
            IntExpr::Add(es) => es.iter().collect(),
            IntExpr::Sub(e1, e2) => vec![e1, e2],
            IntExpr::Mul(es) => es.iter().collect(),
            IntExpr::Div(e1, e2) => vec![e1, e2],
            IntExpr::Mod(e1, e2) => vec![e1, e2],
            IntExpr::Neg(e) => vec![e],
            IntExpr::Abs(e) => vec![e],
            IntExpr::Leq(e1, e2) => vec![e1, e2],
            IntExpr::Lt(e1, e2) => vec![e1, e2],
            IntExpr::Geq(e1, e2) => vec![e1, e2],
            IntExpr::Gt(e1, e2) => vec![e1, e2],
        }
    }

    // fn is_atomic(&self) -> bool {
    //     self.sort() == Sort::Bool
    // }

    fn sort(&self) -> Sort {
        match self {
            IntExpr::Constant(_) | IntExpr::Var(_) => Sort::Int,
            IntExpr::Add(_)
            | IntExpr::Sub(_, _)
            | IntExpr::Mul(_)
            | IntExpr::Div(_, _)
            | IntExpr::Mod(_, _)
            | IntExpr::Neg(_)
            | IntExpr::Abs(_) => Sort::Int,
            IntExpr::Leq(_, _) | IntExpr::Lt(_, _) | IntExpr::Geq(_, _) | IntExpr::Gt(_, _) => {
                Sort::Bool
            }
        }
    }
}

impl Display for IntExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntExpr::Var(v) => write!(f, "{}", v),
            IntExpr::Constant(c) => write!(f, "{}", c),
            IntExpr::Add(es) => {
                write!(f, "(+")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            IntExpr::Sub(e1, e2) => write!(f, "(- {} {})", e1, e2),
            IntExpr::Mul(es) => {
                write!(f, "(*")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            IntExpr::Div(e1, e2) => write!(f, "(div {} {})", e1, e2),
            IntExpr::Mod(e1, e2) => write!(f, "(mod {} {})", e1, e2),
            IntExpr::Neg(e) => write!(f, "(- {})", e),
            IntExpr::Abs(e) => write!(f, "(abs {})", e),
            IntExpr::Leq(e1, e2) => write!(f, "(<= {} {})", e1, e2),
            IntExpr::Lt(e1, e2) => write!(f, "(< {} {})", e1, e2),
            IntExpr::Geq(e1, e2) => write!(f, "(>= {} {})", e1, e2),
            IntExpr::Gt(e1, e2) => write!(f, "(> {} {})", e1, e2),
        }
    }
}
