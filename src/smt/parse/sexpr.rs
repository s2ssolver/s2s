use smt2parser::visitors::SExprVisitor;

use crate::smt::{AstError, Constant, Keyword, SExpr, Symbol};

use super::AstParser;

impl SExprVisitor<Constant, Symbol, Keyword> for AstParser {
    type T = SExpr;

    type E = AstError;

    fn visit_constant_s_expr(&mut self, _value: Constant) -> Result<Self::T, Self::E> {
        todo!()
    }

    fn visit_symbol_s_expr(&mut self, _value: Symbol) -> Result<Self::T, Self::E> {
        todo!()
    }

    fn visit_keyword_s_expr(&mut self, _value: Keyword) -> Result<Self::T, Self::E> {
        todo!()
    }

    fn visit_application_s_expr(&mut self, _values: Vec<Self::T>) -> Result<Self::T, Self::E> {
        todo!()
    }
}
