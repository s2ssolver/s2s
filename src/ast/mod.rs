//! Representation of quantifier free first-order formulas.

mod expr;

mod builder;
pub mod parse;
mod script;

mod error;
pub use builder::ExpressionBuilder;
pub use error::*;
pub use expr::*;
pub use script::*;

/// The maximum character value allowed in the SMT-LIB theory of strings.
const SMT_MAX_CHAR: u32 = 0x2FFFF;

fn convert_smtlib_char(c: char) -> String {
    if c as u32 > SMT_MAX_CHAR {
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
