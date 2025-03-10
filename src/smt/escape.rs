use super::AstError;

pub fn parse_smtlib_string(input: &str, smt25: bool) -> Result<String, AstError> {
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
                            if hex.is_empty() || hex.len() > 5 {
                                return Err(AstError::InvalidEscapeSequence(hex));
                            }
                            match u32::from_str_radix(&hex, 16) {
                                Ok(codepoint) if codepoint <= 0x2FFFF => {
                                    let as_char = char::from_u32(codepoint)
                                        .ok_or(AstError::InvalidCodePoint(codepoint))?;
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
                                        .ok_or(AstError::InvalidCodePoint(codepoint))?;
                                    result.push(as_char);
                                }
                                _ => return Err(AstError::InvalidEscapeSequence(hex)),
                            }
                        }
                    }
                    Some('x') if smt25 => {
                        let mut code = String::new();
                        for _ in 0..2 {
                            code.push(chars.next().unwrap());
                        }
                        let code = match u32::from_str_radix(&code, 16) {
                            Ok(code) => code,
                            Err(_) => {
                                return Err(AstError::InvalidEscapeSequence(format!("\\x{}", code)))
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

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_parse_smt_string_printable_ascii() {
        assert_eq!(parse_smtlib_string("A", false).unwrap(), "A");
        assert_eq!(parse_smtlib_string("Hello", false).unwrap(), "Hello");
        assert_eq!(parse_smtlib_string("12345", false).unwrap(), "12345");
        assert_eq!(parse_smtlib_string("!@#", false).unwrap(), "!@#");
    }

    #[test]
    fn test_parse_smt_string_non_printable_ascii() {
        assert_eq!(parse_smtlib_string("\\u000A", false).unwrap(), "\n");
        assert_eq!(parse_smtlib_string("\\u000D", false).unwrap(), "\r");
        assert_eq!(parse_smtlib_string("\\u0009", false).unwrap(), "\t");
    }

    #[test]
    fn test_parse_smt_string_invalid_escape() {
        let cases = vec!["\\ux", "\\u{abz}", "\\u{110000}, \\u{}"];
        for case in cases {
            assert!(matches!(
                parse_smtlib_string(case, false),
                Err(AstError::InvalidEscapeSequence(_))
            ));
        }
    }

    #[test]
    fn test_parse_smt_string_non_ascii() {
        assert_eq!(parse_smtlib_string("\\u00A9", false).unwrap(), "©");
        assert_eq!(parse_smtlib_string("\\u20AC", false).unwrap(), "€");
        assert_eq!(parse_smtlib_string("\\u{1F600}", false).unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_backslash_no_escape() {
        assert_eq!(parse_smtlib_string("\\L", false).unwrap(), "\\L");
        assert_eq!(parse_smtlib_string("\\n", false).unwrap(), "\\n");
        assert_eq!(parse_smtlib_string("\\r", false).unwrap(), "\\r");
    }

    #[test]
    fn test_parse_smt_25_escape() {
        assert_eq!(parse_smtlib_string("\\xA9", true).unwrap(), "©");
    }

    #[test]
    fn test_parse_no_smt_25_escape() {
        assert_eq!(parse_smtlib_string("\\xA9", false).unwrap(), "\\xA9");
    }

    #[test]
    fn test_parse_smt_string_unicode_escape() {
        assert_eq!(parse_smtlib_string("\\u{10348}", true).unwrap(), "𐍈");
        assert_eq!(parse_smtlib_string("\\u{1F600}", true).unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_unicode_invalid_smt() {
        assert!(parse_smtlib_string("\\u{3FFFF}", true).is_err());
    }

    #[test]
    fn test_parse_smt_string_mixed_string() {
        assert_eq!(parse_smtlib_string("A\\u000AB", true).unwrap(), "A\nB");
        assert_eq!(
            parse_smtlib_string("Hello\\u0020World", true).unwrap(),
            "Hello World"
        );
        assert_eq!(
            parse_smtlib_string("Line1\\u000ALine2", true).unwrap(),
            "Line1\nLine2"
        );
        assert_eq!(
            parse_smtlib_string("Tab\\u0009Space", true).unwrap(),
            "Tab\tSpace"
        );
        assert_eq!(
            parse_smtlib_string("Emoji\\u{1F600}Face", true).unwrap(),
            "Emoji😀Face"
        );
    }

    #[test]
    fn test_parse_smt_string_invalid_escape_sequence() {
        assert!(parse_smtlib_string("\\uXYZ", true).is_err());
        assert!(parse_smtlib_string("\\u{XYZ}", true).is_err());
        assert!(parse_smtlib_string("\\u{110000}", true).is_err()); // Invalid Unicode code point
    }
}
