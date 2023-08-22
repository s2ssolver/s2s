use super::ParseError;

/// Unescape a string literal as specified in the SMT-LIB standard.
/// If `legacy` is true, additionally unescapes unicode escape sequences in SMT-LIB 2.5 syntax (`\xAB` with A, B hex chars).
pub fn unescape(s: &str, legacy: bool) -> Result<Vec<char>, ParseError> {
    let mut res = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('u') => match chars.next() {
                    Some('{') => {
                        let mut code = String::new();
                        #[allow(clippy::while_let_on_iterator)]
                        while let Some(n) = chars.next() {
                            if n == '}' {
                                break;
                            }
                            code.push(n);
                        }
                        let code = u32::from_str_radix(&code, 16).unwrap();
                        res.push(char::from_u32(code).unwrap());
                    }
                    Some(c) => {
                        let mut code = String::new();
                        code.push(c);
                        for _ in 0..4 {
                            code.push(chars.next().unwrap());
                        }
                        let code = u32::from_str_radix(&code, 16).unwrap();
                        res.push(char::from_u32(code).unwrap());
                    }
                    None => {
                        return Err(ParseError::SyntaxError(
                            "Invalid escape sequence".to_string(),
                        ))
                    }
                },
                Some('x') if legacy => {
                    let mut code = String::new();
                    for _ in 0..2 {
                        code.push(chars.next().unwrap());
                    }
                    let code = u32::from_str_radix(&code, 16).unwrap();
                    res.push(char::from_u32(code).unwrap());
                }
                Some(c) => {
                    res.push('\\');
                    res.push(c);
                }
                None => {
                    return Err(ParseError::SyntaxError(
                        "Invalid escape sequence".to_string(),
                    ))
                }
            }
        } else {
            res.push(c);
        }
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::unescape;

    #[test]
    fn basic_unescapes() {
        assert_eq!(
            unescape("hello\\u{21}", false).unwrap(),
            "hello!".chars().collect::<Vec<char>>()
        );
        assert_eq!(
            unescape("\\u{1f600}", false).unwrap(),
            "😀".chars().collect::<Vec<char>>()
        );
        assert_eq!(
            unescape("\\u1f600", false).unwrap(),
            "😀".chars().collect::<Vec<char>>()
        );
    }

    #[test]
    fn smt25_unescapes() {
        assert_eq!(
            unescape("hello\\x21", true).unwrap(),
            "hello!".chars().collect::<Vec<char>>()
        );
        assert_eq!(
            unescape("\\x65", true).unwrap(),
            "e".chars().collect::<Vec<char>>()
        );
    }

    #[test]
    #[should_panic]
    fn invalid_escape_sequence1() {
        _ = unescape("\\u{}", false);
    }

    #[test]
    #[should_panic]
    fn tooshort_escape_sequence() {
        _ = unescape("\\u12", false);
    }

    #[test]
    #[should_panic]
    fn nonhex_escape_sequence() {
        _ = unescape("\\u{12g}", false);
    }

    #[test]
    #[should_panic]
    fn smt25_invalid() {
        assert_eq!(
            unescape("\\xFG", true).unwrap(),
            "e".chars().collect::<Vec<char>>()
        );
    }
}
