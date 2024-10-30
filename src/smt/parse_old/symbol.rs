use smt2parser::visitors;

use crate::smt::{AstError, Symbol};

use super::AstParser;

impl visitors::SymbolVisitor for AstParser {
    type T = Symbol;

    type E = AstError;

    fn visit_fresh_symbol(
        &mut self,
        value: String,
        _kind: visitors::SymbolKind,
    ) -> Result<Self::T, Self::E> {
        Ok(value)
    }
}
