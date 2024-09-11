//! Representation of quantifier free first-order formulas.

mod expr;

mod builder;
mod error;
pub mod nf;
pub mod parse;
mod script;
pub use builder::AstBuilder;
pub use error::*;
pub use expr::*;
pub use script::*;

/// The maximum character value allowed in the SMT-LIB theory of strings.
const SMT_MAX_CHAR: u32 = 0x2FFFF;

pub fn smt_max_char() -> char {
    char::from_u32(SMT_MAX_CHAR).unwrap()
}

fn convert_smtlib_char(c: char) -> String {
    if c as u32 > SMT_MAX_CHAR as u32 {
        panic!("Invalid character in SMT-LIB string: {:?}", c);
    }
    let code_point = c as u32;
    // Check if the character is within the printable ASCII range
    if 0x00020 <= code_point && code_point <= 0x0007E {
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
