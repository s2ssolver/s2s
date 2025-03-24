//! SMT-LIB representation of quantifier free first-order formulas for the theory of strings.

/// Errors that can occur while working with SMT-LIB formulas.
mod error;

mod convert;

/// Representation of SMT-LIB scripts.
mod script;

mod interpret;

//pub use ast::*;
// pub use builder::AstBuilder;
pub use error::*;

pub use script::*;

pub use interpret::Interpreter;
use smt2parser::concrete::SyntaxBuilder;

use crate::node::NodeManager;

pub fn parse_script(
    smt: impl std::io::BufRead,

    mngr: &mut NodeManager,
) -> Result<Script, AstError> {
    let cmds = smt2parser::CommandStream::new(smt, SyntaxBuilder, None);
    let mut converter = convert::Converter::new(mngr);
    let mut script = Script::default();
    for cmd in cmds {
        script.push(converter.convert(cmd?)?);
    }
    Ok(script)
}
