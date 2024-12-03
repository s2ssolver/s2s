mod command;
mod constants;
mod identifier;
mod keyword;
mod sexpr;
mod sort;
mod symbol;
mod term;

use crate::node::{Node, NodeManager, Sort};

use super::{AstError, Script, Symbol};
use super::{Constant, Identifier, Keyword, SExpr, SmtCommand};

use smt2parser::visitors::Smt2Visitor;

pub struct ScriptBuilder<'a> {
    smt25: bool,
    mngr: &'a mut NodeManager,
}

impl<'a> ScriptBuilder<'a> {
    pub fn new(mngr: &'a mut NodeManager) -> Self {
        Self { smt25: false, mngr }
    }

    pub fn parse_script(self, smt: impl std::io::BufRead) -> Result<Script, AstError> {
        let cmds = smt2parser::CommandStream::new(smt, self, None);
        let mut script = Script::default();
        for cmd in cmds {
            script.push(cmd?);
        }
        Ok(script)
    }
}

impl<'a> Smt2Visitor for ScriptBuilder<'a> {
    type Error = AstError;

    type Constant = Constant;

    type QualIdentifier = Identifier;

    type Keyword = Keyword;

    type Sort = Sort;

    type SExpr = SExpr;

    type Symbol = Symbol;

    type Term = Node;

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
