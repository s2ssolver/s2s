use std::{cmp::max, path::PathBuf};

use indexmap::IndexSet;
mod smt2;

use crate::{
    model::formula::{Atom, Formula},
    model::{
        formula::Predicate,
        words::{Pattern, StringTerm, Symbol, WordEquation},
        VarManager,
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
    var_manager: VarManager,
    /// The maximum bound for any variable to check.
    /// If `None`, no bound is set, which will might in an infinite search if the instance is not satisfiable.
    /// If `Some(n)`, the solver will only check for a solution with a bound of `n`.
    /// If no solution is found with every variable bound to `n`, the solver will return `Unsat`.
    ubound: Option<usize>,

    /// The upper bound for each string variable to start the search with   
    start_bound: usize,

    print_model: bool,
}

impl Instance {
    pub fn new(formula: Formula, var_manager: VarManager) -> Self {
        Instance {
            formula,
            var_manager,
            ubound: None,
            start_bound: 1,
            print_model: false,
        }
    }

    pub fn set_ubound(&mut self, bound: usize) {
        self.ubound = Some(bound);
    }

    pub fn set_lbound(&mut self, bound: usize) {
        self.start_bound = bound;
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

    pub fn get_formula_mut(&mut self) -> &mut Formula {
        &mut self.formula
    }

    pub fn get_var_manager(&self) -> &VarManager {
        &self.var_manager
    }

    pub fn get_start_bound(&self) -> usize {
        max(self.start_bound, 1)
    }

    pub fn get_upper_bound(&self) -> Option<usize> {
        self.ubound
    }

    pub fn set_print_model(&mut self, arg: bool) {
        self.print_model = arg;
    }

    pub fn get_print_model(&self) -> bool {
        self.print_model
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
                Parser::Smt2Parser => smt2::parse_smt(input.as_bytes()),
            },
            Err(e) => Err(ParseError::Other(e.to_string(), None)),
        }
    }
}

fn parse_woorpje(input: &str) -> Result<Instance, ParseError> {
    let mut vm = VarManager::new();
    let mut alphabet = IndexSet::new();
    let mut formula = Formula::ttrue();

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
                    vm.new_var(v.to_string().as_str(), crate::model::Sort::String);
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
                    if vm.by_name(c.to_string().as_str()).is_some() {
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
                    } else if let Some(v) = vm.by_name(c.to_string().as_str()) {
                        lhs = StringTerm::concat_var(lhs, v);
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                let mut rhs = StringTerm::empty();
                for c in sides[1].chars() {
                    if alphabet.contains(&c) {
                        rhs = StringTerm::concat_const(rhs, String::from(c).as_str());
                    } else if let Some(v) = vm.by_name(c.to_string().as_str()) {
                        rhs = StringTerm::concat_var(rhs, v);
                    } else {
                        panic!("Unknown symbol in equation '{}'", c);
                    }
                }
                formula = Formula::Predicate(Predicate::Equality(lhs.into(), rhs.into()));
            }
            _ => {}
        }
    }

    Ok(Instance::new(formula, vm))
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
        let vm = instance.get_var_manager();
        assert_eq!(vm.of_sort(crate::model::Sort::String, true).count(), 1);
        let expected_lhs = Pattern::from(vec![
            Symbol::Constant('a'),
            Symbol::Variable(vm.by_name("X").unwrap().clone()),
        ]);
        let expected_lhs =
            StringTerm::concat_var(StringTerm::constant("a"), vm.by_name("X").unwrap());
        let expected_rhs = StringTerm::constant("ab");

        assert_eq!(
            *instance.get_formula(),
            Formula::Predicate(Predicate::Equality(
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
