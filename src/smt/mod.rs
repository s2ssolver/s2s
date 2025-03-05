//! SMT-LIB representation of quantifier free first-order formulas for the theory of strings.

/// Errors that can occur while working with SMT-LIB formulas.
mod error;

mod parse;
pub use parse::ScriptBuilder;

/// Representation of SMT-LIB scripts.
mod script;

mod interpret;

//pub use ast::*;
// pub use builder::AstBuilder;
pub use error::*;

pub use script::*;

pub use interpret::Interpreter;

/// The maximum character value allowed in the SMT-LIB theory of strings.
const SMT_MAX_CHAR: u32 = 0x2FFFF;

pub fn smt_max_char() -> char {
    char::from_u32(SMT_MAX_CHAR).unwrap()
}
