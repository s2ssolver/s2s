use std::io::BufRead;

use indexmap::IndexMap;
use smt2parser::{
    concrete::{self, Constant, QualIdentifier, Sort as SMTSort, Symbol, Term},
    CommandStream,
};

use crate::{
    formula::{Atom, Formula},
    model::{
        words::{Pattern, WordEquation},
        Sort, Variable,
    },
};

use super::{Instance, ParseError};

impl From<smt2parser::Error> for ParseError {
    fn from(e: smt2parser::Error) -> Self {
        match e {
            smt2parser::Error::SyntaxError(pos, msg) => {
                ParseError::SyntaxError(msg, Some((pos.line, pos.column)))
            }
            smt2parser::Error::ParsingError(pos, msg) => {
                ParseError::SyntaxError(msg, Some((pos.line, pos.column)))
            }
        }
    }
}

pub fn parse_smt<R: BufRead>(smt: R) -> Result<Instance, ParseError> {
    let commands = CommandStream::new(
        smt,
        concrete::SyntaxBuilder,
        Some("optional/path/to/file".to_string()),
    );

    let mut variables: IndexMap<String, Variable> = IndexMap::new();
    let mut asserts: Vec<Formula> = Vec::new();
    let mut print_model = false;

    for command in commands {
        let command = command?;

        match &command {
            concrete::Command::Assert { term } => match term {
                Term::Application {
                    qual_identifier,
                    arguments,
                } => {
                    let fm = parse_fun_application(qual_identifier, arguments, &variables)?;
                    asserts.push(fm);
                }
                Term::QualIdentifier(id) => match id {
                    concrete::QualIdentifier::Simple { identifier } => match identifier {
                        smt2parser::visitors::Identifier::Simple { symbol } => {
                            if let Some(v) = variables.get(&symbol.0) {
                                if v.sort() != Sort::Bool {
                                    return Err(ParseError::Other(
                                        format!("Can only assert Boolean variables (found {})", v),
                                        None,
                                    ));
                                }
                                // Add the boolean variable to the list of assertions
                                asserts.push(Formula::Atom(Atom::BoolVar(v.clone())));
                            }
                        }
                        smt2parser::visitors::Identifier::Indexed { .. } => {
                            return Err(ParseError::Other(
                                format!(
                                    "Can only assert Boolean variables (found {})",
                                    identifier.to_string()
                                ),
                                None,
                            ))
                        }
                    },
                    concrete::QualIdentifier::Sorted { identifier, .. } => {
                        return Err(ParseError::Other(
                            format!(
                                "Can only assert Boolean variables (found {})",
                                identifier.to_string()
                            ),
                            None,
                        ))
                    }
                },
                _ => {
                    // Assertion must be function application or Booleans
                    return Err(ParseError::Other(
                        format!("Can not assert {}", term.to_string()),
                        None,
                    ));
                }
            },
            concrete::Command::CheckSat => {
                log::debug!("Unnecessary CheckSat command")
            }
            concrete::Command::DeclareConst { symbol, sort } => {
                let v = parse_var(symbol, sort)?;
                variables.insert(v.name().to_string(), v);
            }
            concrete::Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                if parameters.is_empty() {
                    // This is a constant function, i.e., a variable
                    let v = parse_var(symbol, sort)?;
                    variables.insert(v.name().to_string(), v);
                } else {
                    return Err(ParseError::Unsupported(
                        "Non-constant function declaration".to_string(),
                    ));
                }
            }
            concrete::Command::GetModel => {
                print_model = true;
            }
            concrete::Command::SetLogic { symbol } => {
                // TODO: Check if the logic is supported
                if symbol.0.to_lowercase() != "qf_s" {
                    return Err(ParseError::Unsupported(
                        "QF_S is the only supported logic".to_string(),
                    ));
                }
            }
            _ => return Err(ParseError::Unsupported(command.to_string())),
        }
    }

    let mut instance = match asserts.len() {
        0 => Instance::new(
            Formula::True,
            variables.into_iter().map(|(_, v)| v).collect(),
        ),
        1 => Instance::new(
            asserts.pop().unwrap(),
            variables.into_iter().map(|(_, v)| v).collect(),
        ),
        _ => Instance::new(
            Formula::And(asserts),
            variables.into_iter().map(|(_, v)| v).collect(),
        ),
    };
    instance.set_print_model(print_model);
    Ok(instance)
}

fn convert_sort(sort: &concrete::Sort) -> Result<Sort, ParseError> {
    match sort {
        concrete::Sort::Simple { identifier } => match identifier {
            smt2parser::visitors::Identifier::Simple { symbol } => {
                match symbol.0.to_lowercase().as_str() {
                    "string" => Ok(Sort::String),
                    "int" => Ok(Sort::Int),
                    "bool" => Ok(Sort::Bool),
                    _ => Err(ParseError::Unsupported(format!("Sort {}", symbol.0))),
                }
            }
            smt2parser::visitors::Identifier::Indexed { .. } => {
                Err(ParseError::Unsupported("Indexed sort".to_string()))
            }
        },
        concrete::Sort::Parameterized { .. } => {
            Err(ParseError::Unsupported("Parametrized sort".to_string()))
        }
    }
}

fn parse_var(symbol: &Symbol, sort: &SMTSort) -> Result<Variable, ParseError> {
    let sort = convert_sort(sort)?;
    Ok(Variable::new(symbol.0.clone(), sort))
}

fn parse_fun_application(
    qual_identifier: &QualIdentifier,
    arguments: &Vec<Term>,
    vars: &IndexMap<String, Variable>,
) -> Result<Formula, ParseError> {
    match qual_identifier {
        QualIdentifier::Simple { identifier } => match identifier {
            smt2parser::visitors::Identifier::Simple { symbol } => match symbol.0.as_str() {
                "=" => {
                    if arguments.len() == 2 {
                        let weq = parse_word_equation(&arguments[0], &arguments[1], &vars)?;
                        let atom = Atom::Predicate(crate::formula::Predicate::WordEquation(weq));
                        Ok(Formula::Atom(atom))
                    } else {
                        Err(ParseError::Other(
                            format!("Expected 2 arguments for =, found {}", arguments.len()),
                            None,
                        ))
                    }
                }
                _ => todo!(),
            },
            smt2parser::visitors::Identifier::Indexed {
                symbol: _,
                indices: _,
            } => todo!(), // Needed to regexes
        },
        QualIdentifier::Sorted { identifier, sort } => todo!(),
    }
}

fn parse_word_equation(
    lhs: &Term,
    rhs: &Term,
    vars: &IndexMap<String, Variable>,
) -> Result<WordEquation, ParseError> {
    let lsh = parse_patter(lhs, vars)?;
    let rhs = parse_patter(rhs, vars)?;
    Ok(WordEquation::new(lsh, rhs))
}

fn parse_patter(pat: &Term, vars: &IndexMap<String, Variable>) -> Result<Pattern, ParseError> {
    match pat {
        Term::Constant(Constant::String(s)) => Ok(Pattern::constant(s)),
        Term::QualIdentifier(QualIdentifier::Simple { identifier }) => {
            if let Some(v) = vars.get(&identifier.to_string()) {
                Ok(Pattern::variable(v))
            } else {
                Err(ParseError::UnknownIdentifier(identifier.to_string()))
            }
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if let "str.++" = qual_identifier.to_string().as_str() {
                let mut p = Pattern::empty();
                for t in arguments {
                    p.extend(parse_patter(t, vars)?);
                }
                Ok(p)
            } else {
                return Err(ParseError::Other(
                    format!("Expected str.++, found {}", qual_identifier),
                    None,
                ));
            }
        }
        _ => Err(ParseError::Other(
            format!(
                "Expected string constant, variable, or concatenation, but found {}",
                pat.to_string()
            ),
            None,
        )),
    }
}
