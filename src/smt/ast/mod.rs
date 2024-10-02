use std::{fmt::Display, hash::Hash};

mod core;
mod int;
mod string;

pub use core::CoreExpr;
pub use int::IntExpr;

pub use string::StrExpr;

use super::Sort;

pub trait AstNode {
    /// Returns the children of the node.
    fn children(&self) -> Vec<&Expression>;

    // /// Returns true if the expression is an atomic formula.
    // /// A formula is atomic if it is
    // /// - an equality of two expressions (excluding Boolean equivalences)
    // /// - a Boolean variable
    // /// - a predicate symbol, i.e., an expression of sort Bool
    // fn is_atomic(&self) -> bool;

    /// Returns the sort of the expression.
    /// For function applications, this is the sort of the result.
    /// For variables, this is the sort of the variable.
    /// For constants, the following sorts are returned:
    /// - `true` and `false` have sort Bool
    /// - integer constants have sort Int
    /// - string constants have sort String
    fn sort(&self) -> Sort;
}

/// The root of an SM-LIB expression.
/// This is a vertex in the abstract syntax tree of an SMT-LIB formula.
/// An expression is either a variable or of one of the following types:
/// - Core expressions, i.e., expressions in the theory of Booleans
/// - String expressions, i.e., expressions in the theory of strings
/// - Integer expressions, i.e., expressions in the theory of integers
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Expression {
    Core(Box<CoreExpr>),
    String(Box<StrExpr>),
    Int(Box<IntExpr>),
}

impl Default for Expression {
    fn default() -> Self {
        Expression::Core(Box::new(CoreExpr::Bool(true)))
    }
}

impl AstNode for Expression {
    fn children(&self) -> Vec<&Expression> {
        match self {
            Expression::Core(c) => c.children(),
            Expression::String(s) => s.children(),
            Expression::Int(i) => i.children(),
        }
    }

    // fn is_atomic(&self) -> bool {
    //     match self {
    //         Expression::Var(_) => true,
    //         Expression::Core(c) => c.is_atomic(),
    //         Expression::String(s) => s.is_atomic(),
    //         Expression::Int(i) => i.is_atomic(),
    //     }
    // }

    fn sort(&self) -> Sort {
        match self {
            Expression::Core(c) => c.sort(),
            Expression::String(s) => s.sort(),
            Expression::Int(i) => i.sort(),
        }
    }
}

impl Into<Expression> for CoreExpr {
    fn into(self) -> Expression {
        Expression::Core(Box::new(self))
    }
}

impl Into<Expression> for StrExpr {
    fn into(self) -> Expression {
        Expression::String(Box::new(self))
    }
}

impl Into<Expression> for IntExpr {
    fn into(self) -> Expression {
        Expression::Int(Box::new(self))
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Core(c) => write!(f, "{}", c),
            Expression::String(s) => write!(f, "{}", s),
            Expression::Int(i) => write!(f, "{}", i),
        }
    }
}

// pub struct SubExpressionIterator {
//     stack: Vec<Rc<Expression>>,
// }
// impl Iterator for SubExpressionIterator {
//     type Item = Rc<Expression>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some(expr) = self.stack.pop() {
//             let children: Vec<Rc<Expression>> =
//                 expr.expr.children().into_iter().cloned().collect_vec();
//             self.stack.extend(children);
//             Some(expr)
//         } else {
//             None
//         }
//     }
// }
