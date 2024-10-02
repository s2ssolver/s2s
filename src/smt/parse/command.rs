use smt2parser::visitors::CommandVisitor;

use crate::smt::{AstError, Constant, Expression, Keyword, SExpr, SmtCommand, Sort, Symbol};

use super::AstParser;

impl CommandVisitor<Expression, Symbol, Sort, Keyword, Constant, SExpr> for AstParser {
    type T = SmtCommand;

    type E = AstError;

    fn visit_assert(&mut self, term: Expression) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::Assert(term))
    }

    fn visit_check_sat(&mut self) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::CheckSat)
    }

    fn visit_check_sat_assuming(
        &mut self,
        _literals: Vec<(Symbol, bool)>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("check-sat-assuming".to_string()))
    }

    fn visit_declare_const(&mut self, symbol: Symbol, sort: Sort) -> Result<Self::T, Self::E> {
        match self.declared_vars.insert(symbol.clone(), sort) {
            Some(_) => Err(AstError::AlreadyDeclared(symbol)),
            None => Ok(SmtCommand::DeclareConst(symbol, sort)),
        }
    }

    fn visit_declare_datatype(
        &mut self,
        _symbol: Symbol,
        _datatype: smt2parser::visitors::DatatypeDec<Symbol, Sort>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("declare-datatype".to_string()))
    }

    fn visit_declare_datatypes(
        &mut self,
        _datatypes: Vec<(
            Symbol,
            smt2parser::Numeral,
            smt2parser::visitors::DatatypeDec<Symbol, Sort>,
        )>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("declare-datatypes".to_string()))
    }

    fn visit_declare_fun(
        &mut self,
        symbol: Symbol,
        parameters: Vec<Sort>,
        sort: Sort,
    ) -> Result<Self::T, Self::E> {
        if parameters.is_empty() {
            self.visit_declare_const(symbol, sort)
        } else {
            Err(AstError::Unsupported("non-const declare-fun".to_string()))
        }
    }

    fn visit_declare_sort(
        &mut self,
        _symbol: Symbol,
        _arity: smt2parser::Numeral,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("declare-sort".to_string()))
    }

    fn visit_define_fun(
        &mut self,
        _sig: smt2parser::visitors::FunctionDec<Symbol, Sort>,
        _term: Expression,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("define-fun".to_string()))
    }

    fn visit_define_fun_rec(
        &mut self,
        _sig: smt2parser::visitors::FunctionDec<Symbol, Sort>,
        _term: Expression,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("define-fun-rec".to_string()))
    }

    fn visit_define_funs_rec(
        &mut self,
        _funs: Vec<(smt2parser::visitors::FunctionDec<Symbol, Sort>, Expression)>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("define-funs-rec".to_string()))
    }

    fn visit_define_sort(
        &mut self,
        _symbol: Symbol,
        _parameters: Vec<Symbol>,
        _sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("define-sort".to_string()))
    }

    fn visit_echo(&mut self, message: String) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::Echo(message))
    }

    fn visit_exit(&mut self) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::Exit)
    }

    fn visit_get_assertions(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-assertions".to_string()))
    }

    fn visit_get_assignment(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-assignment".to_string()))
    }

    fn visit_get_info(&mut self, _flag: Keyword) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-info".to_string()))
    }

    fn visit_get_model(&mut self) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::GetModel)
    }

    fn visit_get_option(&mut self, _keyword: Keyword) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-option".to_string()))
    }

    fn visit_get_proof(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-proof".to_string()))
    }

    fn visit_get_unsat_assumptions(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-unsat-assumptions".to_string()))
    }

    fn visit_get_unsat_core(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-unsat-core".to_string()))
    }

    fn visit_get_value(&mut self, _terms: Vec<Expression>) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("get-value".to_string()))
    }

    fn visit_pop(&mut self, _level: smt2parser::Numeral) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("pop".to_string()))
    }

    fn visit_push(&mut self, _level: smt2parser::Numeral) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("push".to_string()))
    }

    fn visit_reset(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("reset".to_string()))
    }

    fn visit_reset_assertions(&mut self) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("reset-assertions".to_string()))
    }

    fn visit_set_info(
        &mut self,
        keyword: Keyword,
        value: smt2parser::visitors::AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E> {
        log::warn!("Ignoring set-info: {} {}", keyword, value);
        Ok(SmtCommand::NoOp)
    }

    fn visit_set_logic(&mut self, symbol: Symbol) -> Result<Self::T, Self::E> {
        Ok(SmtCommand::SetLogic(symbol))
    }

    fn visit_set_option(
        &mut self,
        keyword: Keyword,
        value: smt2parser::visitors::AttributeValue<Constant, Symbol, SExpr>,
    ) -> Result<Self::T, Self::E> {
        log::warn!("Ignoring set-option: {} {}", keyword, value);
        Ok(SmtCommand::NoOp)
    }
}
