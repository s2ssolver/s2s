mod command;
mod constants;
mod identifier;
mod keyword;
mod sexpr;
mod sort;
mod symbol;
mod term;

use std::fmt::Display;

use crate::node::{Node, NodeManager, Sort};

use super::SmtCommand;
use super::{AstError, Script};

use itertools::Itertools;
use smt2parser::visitors::Smt2Visitor;

pub type Symbol = String;

pub type Keyword = String;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Index {
    Num(usize),
    Symbol(Symbol),
}

impl Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Index::Num(n) => write!(f, "{}", n),
            Index::Symbol(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Identifier {
    symbol: Symbol,
    indices: Vec<Index>,
}

impl Identifier {
    pub fn simple(symbol: Symbol) -> Self {
        Self::indexed(symbol, vec![])
    }

    pub fn indexed(symbol: Symbol, indices: Vec<Index>) -> Self {
        Self { symbol, indices }
    }

    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    pub fn indices(&self) -> &[Index] {
        &self.indices
    }
}
impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.indices.is_empty() {
            write!(f, "{}", self.symbol)
        } else {
            write!(f, "(_ {} {})", self.symbol, self.indices.iter().format(" "))
        }
    }
}

pub struct SExpr;
impl Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "")
    }
}

pub enum Constant {
    String(String),
    Int(isize),
    Real(f64),
}

impl Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::String(s) => write!(f, "\"{}\"", s),
            Constant::Int(i) => write!(f, "{}", i),
            Constant::Real(r) => write!(f, "{}", r),
        }
    }
}

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

impl Smt2Visitor for ScriptBuilder<'_> {
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
