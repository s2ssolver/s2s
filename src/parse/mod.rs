use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use indexmap::IndexSet;
mod smt;

use crate::{
    formula::{Atom, Formula},
    model::{
        words::{Pattern, Symbol, WordEquation},
        Variable,
    },
};

#[derive(Clone, Debug, PartialEq)]
pub enum ParseError {
    /// Syntax error, optionally with line and column number
    SyntaxError(String, Option<(usize, usize)>),
    /// Other error, optionally with line and column number
    Other(String, Option<(usize, usize)>),
    /// Unsupported feature
    Unsupported(String),
    /// Unknown identifier
    UnknownIdentifier(String),
    /// File not found
    FileNotFound(String),
}

/// A problem instance, consisting of a formula and a set of variables
/// Should be created using the `parse` module
#[derive(Clone, Debug)]
pub struct Instance {
    /// The formula to solve
    formula: Formula,
    /// The set of all variables
    vars: IndexSet<Variable>,
    /// The maximum bound for any variable to check.
    /// If `None`, no bound is set, which will might in an infinite search if the instance is not satisfiable.
    /// If `Some(n)`, the solver will only check for a solution with a bound of `n`.
    /// If no solution is found with every variable bound to `n`, the solver will return `Unsat`.
    ubound: Option<usize>,

    lbound: usize,
}

impl Instance {
    pub fn new(formula: Formula, vars: IndexSet<Variable>) -> Self {
        Instance {
            formula,
            vars,
            ubound: None,
            lbound: 1,
        }
    }

    pub fn set_ubound(&mut self, bound: usize) {
        self.ubound = Some(bound);
    }

    pub fn set_lbound(&mut self, bound: usize) {
        self.lbound = bound;
    }

    pub fn set_formula(&mut self, formula: Formula) {
        self.formula = formula;
    }

    pub fn remove_bound(&mut self) {
        self.ubound = None;
    }

    pub fn get_formula(&self) -> &Formula {
        &self.formula
    }

    pub fn get_vars(&self) -> &IndexSet<Variable> {
        &self.vars
    }

    pub fn get_lower_bound(&self) -> usize {
        self.lbound
    }

    pub fn get_upper_bound(&self) -> Option<usize> {
        self.ubound
    }
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
                Parser::Smt2Parser => smt::parse_smt(input.as_bytes()),
            },
            Err(e) => Err(ParseError::Other(e.to_string(), None)),
        }
    }
}

fn parse_woorpje(input: &str) -> Result<Instance, ParseError> {
    let mut vars = HashMap::new();
    let mut alphabet = IndexSet::new();
    let mut formula = Formula::True;

    for line in input.lines() {
        let mut tokens = line.split_ascii_whitespace();
        let first = tokens
            .next()
            .ok_or(ParseError::SyntaxError("empty line".to_string(), None))?;
        if first.starts_with('#') {
            // comment
            continue;
        }
        match first {
            "Variables" => {
                let second = tokens.next().ok_or(ParseError::SyntaxError(
                    "missing variables".to_string(),
                    None,
                ))?;
                let varsnames = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or(ParseError::SyntaxError(
                        "Invalid variables".to_string(),
                        None,
                    ))?;
                for v in varsnames.chars() {
                    if alphabet.contains(&v) {
                        panic!("Alphabet cannot contain variables with same name");
                    }
                    let var = Variable::new(v.to_string(), crate::model::Sort::String);
                    vars.insert(v, var.clone());
                }
            }
            "Terminals" => {
                let second = tokens.next().ok_or(ParseError::SyntaxError(
                    "Missing alphabet definition".to_string(),
                    None,
                ))?;
                let alph = second
                    .strip_prefix('{')
                    .and_then(|r| r.strip_suffix('}'))
                    .ok_or(ParseError::SyntaxError(
                        "Invalid alphabet definition".to_string(),
                        None,
                    ))?;
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
                        lhs.append(&Symbol::Constant(c));
                    } else if let Some(v) = vars.get(&c) {
                        lhs.append(&Symbol::Variable(v.clone()));
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                let mut rhs = Pattern::empty();
                for c in sides[1].chars() {
                    if alphabet.contains(&c) {
                        rhs.append(&Symbol::Constant(c));
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
            Symbol::Constant('a'),
            Symbol::Variable(Variable::new("X".to_string(), crate::model::Sort::String)),
        ]);
        let expected_rhs = Pattern::constant("ab");
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
