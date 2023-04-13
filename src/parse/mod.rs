use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use crate::{
    formula::{Atom, Formula},
    model::{
        words::{Pattern, Symbol, WordEquation},
        Variable,
    },
    Instance,
};

pub enum Parser {
    WoorpjeParser,
    Smt2Parser,
}

impl Parser {
    pub fn parse(&self, input: PathBuf) -> Result<Instance, String> {
        let input = std::fs::read_to_string(input).map_err(|e| e.to_string())?;
        match self {
            Parser::WoorpjeParser => parse_woorpje(&input),
            Parser::Smt2Parser => unimplemented!("SMT2 parsing not implemented yet"),
        }
    }
}

fn parse_woorpje(input: &str) -> Result<Instance, String> {
    let mut vars = HashMap::new();
    let mut alphabet = HashSet::new();
    let mut formula = Formula::True;

    for line in input.lines() {
        let mut tokens = line.split_ascii_whitespace();
        let first = tokens.next().ok_or("empty line")?;
        if first.starts_with('#') {
            // comment
            continue;
        }
        match first {
            "Variables" => {
                let second = tokens.next().ok_or("missing variables")?;
                let varsnames = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or("invalid variables")?;
                for v in varsnames.chars() {
                    if alphabet.contains(&v) {
                        panic!("Alphabet cannot contain variables with same name");
                    }
                    let var = Variable::new(v.to_string(), crate::model::Sort::String);
                    vars.insert(v, var.clone());
                }
            }
            "Terminals" => {
                let second = tokens.next().ok_or("missing alphabet")?;
                let alph = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or("invalid alphabet")?;
                alph.chars().for_each(|c| {
                    if vars.contains_key(&c) {
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
                let mut lhs = Pattern::empty();
                for c in sides[0].chars() {
                    if alphabet.contains(&c) {
                        lhs.append(&Symbol::LiteralWord(c.to_string()));
                    } else if let Some(v) = vars.get(&c) {
                        lhs.append(&Symbol::Variable(v.clone()));
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                let mut rhs = Pattern::empty();
                for c in sides[1].chars() {
                    if alphabet.contains(&c) {
                        rhs.append(&Symbol::LiteralWord(c.to_string()));
                    } else if let Some(v) = vars.get(&c) {
                        rhs.append(&Symbol::Variable(v.clone()));
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                formula = Formula::Atom(Atom::word_equation(WordEquation::new(lhs, rhs)));
            }
            _ => {}
        }
    }

    Ok(Instance::new(formula, vars.values().cloned().collect()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_woorpje_valid() {
        let input = r#"Variables {X}
Terminals {ab}
Equation: aX = ab"#;

        let instance = parse_woorpje(input).unwrap();
        assert_eq!(instance.get_vars().len(), 1);
        let expected_lhs = Pattern::from(vec![
            Symbol::LiteralWord("a".to_string()),
            Symbol::Variable(Variable::new("X".to_string(), crate::model::Sort::String)),
        ]);
        let expected_rhs = Pattern::from(vec![
            Symbol::LiteralWord("a".to_string()),
            Symbol::LiteralWord("b".to_string()),
        ]);
        let expected_eq = WordEquation::new(expected_lhs, expected_rhs);
        assert_eq!(
            *instance.get_formula(),
            Formula::Atom(Atom::word_equation(expected_eq))
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
