use smt2parser::visitors;

use super::ScriptBuilder;

impl visitors::KeywordVisitor for ScriptBuilder<'_> {
    type T = String;

    type E = super::AstError;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(value)
    }
}
