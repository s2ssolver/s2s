//! SMT-LIB representation of quantifier free first-order formulas for the theory of strings.

/// Errors that can occur while working with SMT-LIB formulas.
mod error;

mod parse;
pub use parse::ScriptBuilder;

/// Representation of SMT-LIB scripts.
mod script;

use std::fmt::Display;

//pub use ast::*;
// pub use builder::AstBuilder;
pub use error::*;
use itertools::Itertools;
pub use script::*;

/// The maximum character value allowed in the SMT-LIB theory of strings.
const SMT_MAX_CHAR: u32 = 0x2FFFF;

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

/// The sort of an expression.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Sort {
    Bool,
    Int,
    String,
    RegLan,
}

#[allow(unused)]
impl Sort {
    pub fn is_bool(&self) -> bool {
        matches!(self, Sort::Bool)
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Sort::Int)
    }

    pub fn is_string(&self) -> bool {
        matches!(self, Sort::String)
    }

    pub fn is_reglan(&self) -> bool {
        matches!(self, Sort::RegLan)
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::String => write!(f, "String"),
            Sort::RegLan => write!(f, "RegLang"),
        }
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

pub fn smt_max_char() -> char {
    char::from_u32(SMT_MAX_CHAR).unwrap()
}

fn _convert_smtlib_char(c: char) -> String {
    if c as u32 > SMT_MAX_CHAR {
        panic!("Invalid character in SMT-LIB string: {:?}", c);
    }
    let code_point = c as u32;
    // Check if the character is within the printable ASCII range
    if (0x00020..=0x0007E).contains(&code_point) {
        // Printable ASCII characters or space can be printed directly
        c.to_string()
    } else {
        // Otherwise, escape the character
        if code_point <= 0xFFFF {
            format!("\\u{:04X}", code_point)
        } else {
            format!("\\u{{{:X}}}", code_point)
        }
    }
}
