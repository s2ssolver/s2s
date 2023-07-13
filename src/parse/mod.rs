use std::path::PathBuf;

use indexmap::IndexSet;
mod smt2;
mod util;

use crate::{
    instance::Instance,
    model::{formula::Formula, Sort, Variable},
    model::{formula::Predicate, terms::StringTerm},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParseError {
    /// Syntax error, optionally with line and column number
    SyntaxError(String),
    /// Other error, optionally with line and column number
    Other(String),
    /// Unsupported feature
    Unsupported(String),
    /// Unknown identifier
    UnknownIdentifier(String),
    /// File not found
    FileNotFound(String),
}

pub enum Parser {
    WoorpjeParser,
    Smt2Parser,
}

impl Parser {
    pub fn parse(&self, input: PathBuf) -> Result<Instance, ParseError> {
        match std::fs::read_to_string(input) {
            Ok(input) => match self {
                Parser::WoorpjeParser => parse_woorpje(&input),
                Parser::Smt2Parser => smt2::parse_smt(input.as_bytes()),
            },
            Err(e) => Err(ParseError::Other(e.to_string())),
        }
    }
}

fn parse_woorpje(input: &str) -> Result<Instance, ParseError> {
    let mut instance = Instance::default();
    let mut alphabet = IndexSet::new();
    let mut formula = Formula::ttrue();

    for line in input.lines() {
        let mut tokens = line.split_ascii_whitespace();
        let first = tokens
            .next()
            .ok_or(ParseError::SyntaxError("empty line".to_string()))?;
        if first.starts_with('#') {
            // comment
            continue;
        }
        match first {
            "Variables" => {
                let second = tokens
                    .next()
                    .ok_or(ParseError::SyntaxError("missing variables".to_string()))?;
                let varsnames = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or(ParseError::SyntaxError("Invalid variables".to_string()))?;
                for v in varsnames.chars() {
                    if alphabet.contains(&v) {
                        panic!("Alphabet cannot contain variables with same name");
                    }
                    let v = Variable::new(v.to_string(), Sort::String);
                    instance.add_var(v);
                }
            }
            "Terminals" => {
                let second = tokens.next().ok_or(ParseError::SyntaxError(
                    "Missing alphabet definition".to_string(),
                ))?;
                let alph = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or(ParseError::SyntaxError(
                        "Invalid alphabet definition".to_string(),
                    ))?;
                alph.chars().for_each(|c| {
                    if instance.var_by_name(c.to_string().as_str()).is_some() {
                        panic!("Alphabet cannot contain variables with same name");
                    }
                    alphabet.insert(c);
                });
            }
            "Equation:" => {
                let second: String = tokens.collect();
                let sides: Vec<&str> = second.split('=').collect();
                assert!(
                    sides.len() == 2,
                    "Must have exactly one '=' in an equation. Was: '{}'",
                    second
                );
                let mut lhs = StringTerm::empty();
                for c in sides[0].chars() {
                    if alphabet.contains(&c) {
                        lhs = StringTerm::concat_const(lhs, String::from(c).as_str());
                    } else if let Some(v) = instance.var_by_name(c.to_string().as_str()) {
                        lhs = StringTerm::concat_var(lhs, v);
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                let mut rhs = StringTerm::empty();
                for c in sides[1].chars() {
                    if alphabet.contains(&c) {
                        rhs = StringTerm::concat_const(rhs, String::from(c).as_str());
                    } else if let Some(v) = instance.var_by_name(c.to_string().as_str()) {
                        rhs = StringTerm::concat_var(rhs, v);
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                formula = Formula::predicate(Predicate::Equality(lhs.into(), rhs.into()));
            }
            _ => {}
        }
    }
    instance.set_formula(formula);
    Ok(instance)
}

#[cfg(test)]
mod tests {

    use crate::model::{terms::StringTerm, Sort};

    use super::*;

    #[test]
    fn parse_woorpje_valid() {
        let input = r#"Variables {X}
Terminals {ab}
Equation: aX = ab"#;

        let instance = parse_woorpje(input).unwrap();

        assert_eq!(instance.vars_of_sort(Sort::String).count(), 1);

        let expected_lhs = StringTerm::concat_var(
            StringTerm::constant("a"),
            instance.var_by_name("X").unwrap(),
        );
        let expected_rhs = StringTerm::constant("ab");

        assert_eq!(
            *instance.get_formula(),
            Formula::predicate(Predicate::Equality(
                expected_lhs.into(),
                expected_rhs.into()
            ))
        );
    }

    #[test]
    #[should_panic]
    fn parse_woorpje_invalid_eq() {
        let input = r#"Variables {X}
Terminals {ab}
Equation: aX = ab = X"#;
        parse_woorpje(input).unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_woorpje_invalid_chars() {
        let input = r#"Variables {X}
Terminals {abX}
Equation: aX = ab"#;
        parse_woorpje(input).unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_woorpje_unknown_var() {
        let input = r#"Variables {X}
Terminals {ab}
Equation: aX = Yb"#;
        parse_woorpje(input).unwrap();
    }

    #[test]
    #[should_panic]
    fn parse_woorpje_unknown_const() {
        let input = r#"Variables {X}
Terminals {ab}
Equation: aX = cb"#;
        parse_woorpje(input).unwrap();
    }
}
