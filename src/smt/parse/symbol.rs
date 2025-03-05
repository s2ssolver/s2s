use smt2parser::visitors;

use super::Symbol;
use crate::smt::AstError;

use super::ScriptBuilder;

impl visitors::SymbolVisitor for ScriptBuilder<'_> {
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
