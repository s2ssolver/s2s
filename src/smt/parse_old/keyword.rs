use smt2parser::visitors;

use super::AstParser;

impl visitors::KeywordVisitor for AstParser {
    type T = String;

    type E = super::AstError;

    fn visit_keyword(&mut self, value: String) -> Result<Self::T, Self::E> {
        Ok(value)
    }
}
