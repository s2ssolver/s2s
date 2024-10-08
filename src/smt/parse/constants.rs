use num_traits::cast::ToPrimitive;
use smt2parser::visitors;

use crate::smt::{AstError, Constant};

use super::AstParser;

impl AstParser {
    fn parse_smtlib_string(&self, input: &str) -> Result<String, AstError> {
        let mut chars = input.chars().peekable();
        let mut result = String::with_capacity(input.len());
        let mut buffer = String::new();
        while let Some(c) = chars.next() {
            match c {
                '\\' => {
                    if !buffer.is_empty() {
                        result.push_str(&buffer);
                        buffer.clear();
                    }
                    match chars.next() {
                        Some('u') => {
                            if chars.peek() == Some(&'{') {
                                // Long form \u{d₀}...\u{d₄d₃d₂d₁d₀}
                                chars.next();
                                let mut hex = String::new();
                                while let Some(&next) = chars.peek() {
                                    if next == '}' {
                                        break;
                                    }
                                    hex.push(next);
                                    chars.next();
                                }
                                chars.next(); // consume '}'
                                if hex.len() < 1 || hex.len() > 5 {
                                    return Err(AstError::InvalidEscapeSequence(hex));
                                }
                                match u32::from_str_radix(&hex, 16) {
                                    Ok(codepoint) if codepoint <= 0x2FFFF => {
                                        let as_char = char::from_u32(codepoint)
                                            .ok_or_else(|| AstError::InvalidCodePoint(codepoint))?;
                                        result.push(as_char);
                                    }
                                    _ => return Err(AstError::InvalidEscapeSequence(hex)),
                                }
                            } else {
                                // Short form \ud₃d₂d₁d₀
                                let mut hex = String::new();
                                for _ in 0..4 {
                                    if let Some(h) = chars.next() {
                                        hex.push(h);
                                    } else {
                                        return Err(AstError::InvalidEscapeSequence(hex));
                                    }
                                }
                                match u32::from_str_radix(&hex, 16) {
                                    Ok(codepoint) => {
                                        let as_char = char::from_u32(codepoint)
                                            .ok_or_else(|| AstError::InvalidCodePoint(codepoint))?;
                                        result.push(as_char);
                                    }
                                    _ => return Err(AstError::InvalidEscapeSequence(hex)),
                                }
                            }
                        }
                        Some('x') if self.smt25 => {
                            let mut code = String::new();
                            for _ in 0..2 {
                                code.push(chars.next().unwrap());
                            }
                            let code = match u32::from_str_radix(&code, 16) {
                                Ok(code) => code,
                                Err(_) => {
                                    return Err(AstError::InvalidEscapeSequence(format!(
                                        "\\x{}",
                                        code
                                    )))
                                }
                            };
                            result.push(char::from_u32(code).unwrap());
                        }
                        Some(c) => {
                            result.push('\\');
                            result.push(c);
                        }
                        None => result.push('\\'),
                    }
                }
                '"' => buffer.push('"'), // Double " is escaped as ", but the parser seems to handle this already
                c if (0x20..=0x7E).contains(&(c as u32)) => {
                    buffer.push(c);
                }
                c => return Err(AstError::InvalidCodePoint(c as u32)),
            }
        }

        if !buffer.is_empty() {
            result.push_str(&buffer);
        }

        Ok(result)
    }
}

impl visitors::ConstantVisitor for AstParser {
    type T = Constant;

    type E = AstError;

    fn visit_numeral_constant(&mut self, value: smt2parser::Numeral) -> Result<Self::T, Self::E> {
        value
            .to_isize()
            .map(|n| Constant::Int(n))
            .ok_or(AstError::NumeralOutOfBounds(value))
    }

    fn visit_string_constant(&mut self, value: String) -> Result<Self::T, Self::E> {
        self.parse_smtlib_string(&value).map(Constant::String)
    }

    fn visit_decimal_constant(&mut self, value: smt2parser::Decimal) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported(format!(
            "Decimal constant: {}",
            value
        )))
    }

    fn visit_hexadecimal_constant(
        &mut self,
        value: smt2parser::Hexadecimal,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported(format!(
            "Hexadecimal constant: {:?}",
            value
        )))
    }

    fn visit_binary_constant(&mut self, value: smt2parser::Binary) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported(format!(
            "Binary constant: {:?}",
            value
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_smt_string_printable_ascii() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("A").unwrap(), "A");
        assert_eq!(parser.parse_smtlib_string("Hello").unwrap(), "Hello");
        assert_eq!(parser.parse_smtlib_string("12345").unwrap(), "12345");
        assert_eq!(parser.parse_smtlib_string("!@#").unwrap(), "!@#");
    }

    #[test]
    fn test_parse_smt_string_non_printable_ascii() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("\\u000A").unwrap(), "\n");
        assert_eq!(parser.parse_smtlib_string("\\u000D").unwrap(), "\r");
        assert_eq!(parser.parse_smtlib_string("\\u0009").unwrap(), "\t");
    }

    #[test]
    fn test_parse_smt_string_invalid_escape() {
        let parser = AstParser::default();

        let cases = vec!["\\ux", "\\u{abz}", "\\u{110000}, \\u{}"];
        for case in cases {
            assert!(matches!(
                parser.parse_smtlib_string(case),
                Err(AstError::InvalidEscapeSequence(_))
            ));
        }
    }

    #[test]
    fn test_parse_smt_string_non_ascii() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("\\u00A9").unwrap(), "©");
        assert_eq!(parser.parse_smtlib_string("\\u20AC").unwrap(), "€");
        assert_eq!(parser.parse_smtlib_string("\\u{1F600}").unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_backslash_no_escape() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("\\L").unwrap(), "\\L");
        assert_eq!(parser.parse_smtlib_string("\\n").unwrap(), "\\n");
        assert_eq!(parser.parse_smtlib_string("\\r").unwrap(), "\\r");
    }

    #[test]
    fn test_parse_smt_25_escape() {
        let mut parser = AstParser::default();
        parser.smt25 = true;
        assert_eq!(parser.parse_smtlib_string("\\xA9").unwrap(), "©");
    }

    #[test]
    fn test_parse_no_smt_25_escape() {
        let mut parser = AstParser::default();
        parser.smt25 = false;
        assert_eq!(parser.parse_smtlib_string("\\xA9").unwrap(), "\\xA9");
    }

    #[test]
    fn test_parse_smt_string_unicode_escape() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("\\u{10348}").unwrap(), "𐍈");
        assert_eq!(parser.parse_smtlib_string("\\u{1F600}").unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_unicode_invalid_smt() {
        let parser = AstParser::default();
        assert!(parser.parse_smtlib_string("\\u{3FFFF}").is_err());
    }

    #[test]
    fn test_parse_smt_string_mixed_string() {
        let parser = AstParser::default();
        assert_eq!(parser.parse_smtlib_string("A\\u000AB").unwrap(), "A\nB");
        assert_eq!(
            parser.parse_smtlib_string("Hello\\u0020World").unwrap(),
            "Hello World"
        );
        assert_eq!(
            parser.parse_smtlib_string("Line1\\u000ALine2").unwrap(),
            "Line1\nLine2"
        );
        assert_eq!(
            parser.parse_smtlib_string("Tab\\u0009Space").unwrap(),
            "Tab\tSpace"
        );
        assert_eq!(
            parser.parse_smtlib_string("Emoji\\u{1F600}Face").unwrap(),
            "Emoji😀Face"
        );
    }

    #[test]
    fn test_parse_smt_string_invalid_escape_sequence() {
        let parser = AstParser::default();
        assert!(parser.parse_smtlib_string("\\uXYZ").is_err());
        assert!(parser.parse_smtlib_string("\\u{XYZ}").is_err());
        assert!(parser.parse_smtlib_string("\\u{110000}").is_err()); // Invalid Unicode code point
    }
}
