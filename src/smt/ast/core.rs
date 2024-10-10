use std::fmt::Display;

use crate::smt::{Sort, Symbol};

use super::{AstNode, Expression};

/// The SMT-LIB core expressions
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum CoreExpr {
    /// A boolean variable
    Var(Symbol),
    /// A boolean constant
    Bool(bool),
    /// Boolean Negation
    Not(Expression),
    /// Boolean Conjunction
    And(Vec<Expression>),
    /// Boolean Disjunction
    Or(Vec<Expression>),
    /// Boolean Equivalence
    Equal(Expression, Expression),
    /// Boolean Implication
    Imp(Expression, Expression),
    /// If-then-else
    Ite(Expression, Expression, Expression),
    /// Distinct
    Distinct(Vec<Expression>),
}

impl AstNode for CoreExpr {
    fn children(&self) -> Vec<&Expression> {
        match self {
            CoreExpr::Bool(_) | CoreExpr::Var(_) => vec![],
            CoreExpr::Not(e) => vec![e],
            CoreExpr::And(es) => es.iter().collect(),
            CoreExpr::Or(es) => es.iter().collect(),
            CoreExpr::Equal(e1, e2) => vec![e1, e2],
            CoreExpr::Imp(e1, e2) => vec![e1, e2],
            CoreExpr::Ite(i, t, e) => vec![i, t, e],
            CoreExpr::Distinct(es) => es.iter().collect(),
        }
    }

    // fn is_atomic(&self) -> bool {
    //     match self {
    //         CoreExpr::Bool(_) => true,
    //         CoreExpr::Equal(r1, e2) => true,
    //         _ => false,
    //     }
    // }

    fn sort(&self) -> Sort {
        match self {
            CoreExpr::Bool(_) | CoreExpr::Var(_) => Sort::Bool,
            CoreExpr::Not(_)
            | CoreExpr::And(_)
            | CoreExpr::Imp(_, _)
            | CoreExpr::Or(_)
            | CoreExpr::Distinct(_) => Sort::Bool,
            CoreExpr::Equal(l, r) => {
                assert!(
                    l.sort() == r.sort(),
                    "Sort mismatch for {}: {:?} != {:?}",
                    self,
                    l.sort(),
                    r.sort(),
                );
                Sort::Bool
            }
            CoreExpr::Ite(_, t, e) => {
                let t_sort = t.sort();
                let e_sort = e.sort();
                assert!(
                    t_sort == e_sort,
                    "Sort mismatch for {}: {:?} != {:?}",
                    self,
                    t_sort,
                    e_sort
                );
                t_sort
            }
        }
    }
}

impl Display for CoreExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoreExpr::Var(v) => write!(f, "{}", v),
            CoreExpr::Bool(b) => write!(f, "{}", b),
            CoreExpr::Not(e) => write!(f, "(not {})", e),
            CoreExpr::And(es) => {
                write!(f, "(and")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }

            CoreExpr::Or(es) => {
                write!(f, "(or")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            CoreExpr::Equal(e1, e2) => write!(f, "(= {} {})", e1, e2),
            CoreExpr::Imp(e1, e2) => write!(f, "(=> {} {})", e1, e2),
            CoreExpr::Ite(i, t, e) => write!(f, "(ite {} {} {})", i, t, e),
            CoreExpr::Distinct(es) => {
                write!(f, "(distinct")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}
