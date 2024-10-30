mod command;
mod constants;
mod identifier;
mod keyword;
mod sexpr;
mod sort;
mod symbol;
mod term;

use super::{ast::Expression, Constant, Identifier, Keyword, SExpr, SmtCommand, Sort};
use super::{AstError, Script, Symbol};

use indexmap::IndexMap;
use smt2parser::visitors::Smt2Visitor;

pub struct AstParser {
    smt25: bool,
    declared_vars: IndexMap<Symbol, Sort>,
}
impl Default for AstParser {
    fn default() -> Self {
        Self {
            smt25: false,
            declared_vars: IndexMap::new(),
        }
    }
}

impl AstParser {
    pub fn parse_script(self, smt: impl std::io::BufRead) -> Result<Script, AstError> {
        let cmds = smt2parser::CommandStream::new(smt, self, None);
        let mut script = Script::default();
        for cmd in cmds {
            script.push(cmd?);
        }
        Ok(script)
    }
}

impl Smt2Visitor for AstParser {
    type Error = AstError;

    type Constant = Constant;

    type QualIdentifier = Identifier;

    type Keyword = Keyword;

    type Sort = Sort;

    type SExpr = SExpr;

    type Symbol = Symbol;

    type Term = Expression;

    type Command = SmtCommand;

    fn syntax_error(&mut self, position: smt2parser::Position, s: String) -> Self::Error {
        AstError::SyntaxError {
            position,
            message: s,
        }
    }

    fn parsing_error(&mut self, position: smt2parser::Position, s: String) -> Self::Error {
        AstError::SyntaxError {
            position,
            message: s,
        }
    }
}
