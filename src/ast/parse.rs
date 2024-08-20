use std::{path::Path, rc::Rc};

use crate::context::Context;

use super::{
    expr::{ExprType, Expression, Sort, StrExpr, Variable},
    script::Script,
};
use super::{AstError, ExpressionBuilder};

use itertools::Itertools;

use num_traits::cast::ToPrimitive;
use regulaer::re::{ReBuilder, Regex};
use smt2parser::visitors::Index;
use smt2parser::{
    concrete::{Command, Constant, QualIdentifier, SyntaxBuilder, Term},
    visitors::Identifier,
    CommandStream,
};

pub fn parse_script_file(
    path: &Path,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
) -> Result<Script, AstError> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    parse_script(reader, ctx, builder)
}

pub fn parse_script(
    input: impl std::io::BufRead,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
) -> Result<Script, AstError> {
    let cmds = CommandStream::new(input, SyntaxBuilder, None);
    let mut script = Script::default();
    let cmds = cmds.collect::<Result<Vec<_>, _>>()?;

    for cmd in cmds {
        match cmd {
            Command::Assert { term } => {
                let expr = convert_term(&term, ctx, builder)?;
                script.assert(expr);
            }
            Command::CheckSat => script.check_sat(),
            Command::DeclareConst { symbol, sort } => {
                let sort = convert_sort(&sort)?;
                let var = ctx
                    .new_var(symbol.0.to_owned(), sort)
                    .ok_or(AstError::Unsupported(format!("{}", symbol)))?;
                script.declare_var(var);
            }
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } if parameters.is_empty() => {
                let sort = convert_sort(&sort)?;
                let var = ctx
                    .new_var(symbol.0.to_owned(), sort)
                    .ok_or(AstError::Unsupported(format!("{}", symbol)))?;
                script.declare_var(var);
            }
            Command::Echo { .. } => {}
            Command::Exit => {}
            Command::GetModel => script.get_model(),
            Command::SetLogic { symbol } => script.set_logic(symbol.0.to_owned()),
            Command::SetOption { .. } => {}
            _ => return Err(AstError::Unsupported(format!("{}", cmd))),
        }
    }

    Ok(script)
}

fn convert_term(
    term: &Term,
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
) -> Result<Rc<Expression>, AstError> {
    match term {
        Term::Constant(c) => match c {
            Constant::String(s) => {
                let parsed = parse_smtlib_string(s)?;
                Ok(builder.string(parsed))
            }
            Constant::Numeral(n) => n
                .to_isize()
                .map(|n| builder.int(n))
                .ok_or(AstError::Unsupported(format!("{}", n))),
            _ => Err(AstError::Unsupported(format!("{}", c))),
        },
        Term::QualIdentifier(i) => {
            let var = convert_variable(i, ctx)?;
            Ok(builder.var(var))
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => convert_application(qual_identifier, arguments, ctx, builder),
        _ => Err(AstError::Unsupported(format!("{}", term))),
    }
}

fn parse_smtlib_string(input: &str) -> Result<String, AstError> {
    let mut chars = input.chars().peekable();
    let mut result = String::with_capacity(input.len());

    let mut buffer = String::new();
    while let Some(c) = chars.next() {
        match c {
            '"' => {
                if chars.peek() == Some(&'"') {
                    // Handle double quote escape sequence
                    chars.next();
                    result.push('"');
                } else {
                    if !buffer.is_empty() {
                        result.push_str(&buffer);
                        buffer.clear();
                    }
                }
            }
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
                    Some(c) => return Err(AstError::InvalidEscapeSequence(format!("\\{c}"))),
                    None => return Err(AstError::InvalidEscapeSequence("\\".to_string())),
                }
            }
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

fn convert_variable(
    identifier: &QualIdentifier,
    ctx: &mut Context,
) -> Result<Rc<Variable>, AstError> {
    let identifier = match identifier {
        QualIdentifier::Simple { identifier } => identifier,
        QualIdentifier::Sorted { identifier, .. } => identifier,
    };
    match identifier {
        Identifier::Simple { symbol } => {
            let name = symbol.0.to_owned();

            ctx.get_var(&name).ok_or(AstError::Undeclared(name))
        }
        Identifier::Indexed { .. } => Err(AstError::Unsupported(identifier.to_string())),
    }
}

fn convert_application(
    qual_identifier: &QualIdentifier,
    arguments: &[Term],
    ctx: &mut Context,
    builder: &mut ExpressionBuilder,
) -> Result<Rc<Expression>, AstError> {
    let identifier = match qual_identifier {
        QualIdentifier::Simple { identifier } => identifier,
        QualIdentifier::Sorted { identifier, .. } => identifier,
    };

    match identifier {
        Identifier::Simple { symbol } => {
            if symbol.0 == "str.in_re" || symbol.0 == "str.in.re" {
                assert!(arguments.len() == 2);
                let pat = convert_term(&arguments[0], ctx, builder)?;
                let re = convert_re(ctx, &arguments[1], builder)?;
                let re = builder.regex(re);
                Ok(builder.in_re(pat, re))
            } else {
                let args = arguments
                    .iter()
                    .map(|arg| convert_term(arg, ctx, builder))
                    .collect::<Result<Vec<_>, _>>()?;
                smt2expr(&symbol.0, args, builder)
            }
        }
        Identifier::Indexed { .. } => Err(AstError::Unsupported(identifier.to_string())),
    }
}

fn convert_re(
    ctx: &mut Context,
    term: &Term,
    builder: &mut ExpressionBuilder,
) -> Result<Regex, AstError> {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let (name, indices) = match qual_identifier {
                QualIdentifier::Simple { identifier }
                | QualIdentifier::Sorted { identifier, .. } => match identifier {
                    Identifier::Simple { symbol } => (&symbol.0, vec![]),
                    Identifier::Indexed { symbol, indices } => (&symbol.0, indices.clone()),
                },
            };
            match name.as_str() {
                "str.to_re" | "str.to.re" if arguments.len() == 1 => {
                    let s_term = convert_term(&arguments[0], ctx, builder)?;
                    let s = if let ExprType::String(StrExpr::Constant(s)) = s_term.get_type() {
                        s
                    } else {
                        return Err(AstError::Unsupported(format!(
                            "Regex string '{}'",
                            arguments[0]
                        )));
                    };
                    Ok(builder.re_builder().word(s.clone().into()))
                }
                "re.range" => {
                    assert!(arguments.len() == 2);
                    let s_term = convert_term(&arguments[0], ctx, builder)?;
                    let start = if let ExprType::String(StrExpr::Constant(s)) = s_term.get_type() {
                        s
                    } else {
                        return Err(AstError::Unsupported(format!(
                            "Regex range start '{}'",
                            arguments[0]
                        )));
                    };
                    let e_term = convert_term(&arguments[1], ctx, builder)?;
                    let end = if let ExprType::String(StrExpr::Constant(s)) = e_term.get_type() {
                        s
                    } else {
                        return Err(AstError::Unsupported(format!(
                            "Regex range end '{}'",
                            arguments[1]
                        )));
                    };
                    if start.len() != 1 || end.len() != 1 {
                        Ok(builder.re_builder().none())
                    } else {
                        Ok(builder
                            .re_builder()
                            .range(start.chars().next().unwrap(), end.chars().next().unwrap()))
                    }
                }
                "re.++" => {
                    let args = arguments
                        .iter()
                        .map(|arg| convert_re(ctx, arg, builder))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(builder.re_builder().concat(args))
                }
                "re.union" => {
                    let args = arguments
                        .iter()
                        .map(|arg| convert_re(ctx, arg, builder))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(builder.re_builder().union(args))
                }
                "re.inter" => {
                    let args = arguments
                        .iter()
                        .map(|arg| convert_re(ctx, arg, builder))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(builder.re_builder().inter(args))
                }
                "re.*" if arguments.len() == 1 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    Ok(builder.re_builder().star(arg))
                }
                "re.+" if arguments.len() == 1 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    Ok(builder.re_builder().plus(arg))
                }
                "re.opt" if arguments.len() == 1 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    Ok(builder.re_builder().opt(arg))
                }
                "re.comp" if arguments.len() == 1 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    Ok(builder.re_builder().comp(arg))
                }
                "re.loop" if arguments.len() == 1 && indices.len() == 2 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    let lower = if let Index::Numeral(n) = &indices[0] {
                        n.to_usize()
                            .ok_or(AstError::Unsupported(format!("{}", n)))?
                    } else {
                        return Err(AstError::Unsupported(format!("{:?}", indices[0])));
                    };
                    let upper = if let Index::Numeral(n) = &indices[1] {
                        n.to_usize()
                            .ok_or(AstError::Unsupported(format!("{}", n)))?
                    } else {
                        return Err(AstError::Unsupported(format!("{:?}", indices[1])));
                    };

                    Ok(builder.re_builder().loop_(arg, lower, upper))
                }
                "re.^" if arguments.len() == 1 && indices.len() == 1 => {
                    let arg = convert_re(ctx, &arguments[0], builder)?;
                    let n = if let Index::Numeral(n) = &indices[0] {
                        n.to_usize()
                            .ok_or(AstError::Unsupported(format!("{}", n)))?
                    } else {
                        return Err(AstError::Unsupported(format!("{:?}", indices[0])));
                    };

                    Ok(builder.re_builder().pow(arg, n))
                }

                _ => Err(AstError::Unsupported(term.to_string())),
            }
        }
        Term::QualIdentifier(QualIdentifier::Simple { identifier }) => match identifier {
            Identifier::Simple { symbol } => match symbol.0.as_str() {
                "re.all" => Ok(builder.re_builder().all()),
                "re.none" => Ok(builder.re_builder().none()),
                "re.allchar" => Ok(builder.re_builder().any_char()),
                _ => Err(AstError::Unsupported(format!("{}", symbol))),
            },
            Identifier::Indexed { .. } => Err(AstError::Unsupported(format!("{:?}", term))),
        },
        _ => Err(AstError::Unsupported(format!("{:?}", term))),
    }
}

fn smt2expr(
    name: &str,
    args: Vec<Rc<Expression>>,
    builder: &mut ExpressionBuilder,
) -> Result<Rc<Expression>, AstError> {
    match name {
        // Core
        "not" if args.len() == 1 => Ok(builder.not(args[0].clone())),
        "and" => Ok(builder.and(args)),
        "or" => Ok(builder.or(args)),
        "=>" if args.len() == 2 => Ok(builder.imp(args[0].clone(), args[1].clone())),
        "=" if args.len() == 2 => Ok(builder.eq(args[0].clone(), args[1].clone())),
        "ite" if args.len() == 3 => {
            Ok(builder.ite(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "distinct" => Ok(builder.distinct(args)),
        // String
        "str.++" => Ok(builder.concat(args)),
        "str.len" if args.len() == 1 => Ok(builder.length(args[0].clone())),
        "str.substr" if args.len() == 3 => {
            Ok(builder.substr(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.at" if args.len() == 2 => Ok(builder.str_at(args[0].clone(), args[1].clone())),
        "str.prefixof" if args.len() == 2 => {
            Ok(builder.prefix_of(args[0].clone(), args[1].clone()))
        }
        "str.suffixof" if args.len() == 2 => {
            Ok(builder.suffix_of(args[0].clone(), args[1].clone()))
        }
        "str.contains" if args.len() == 2 => Ok(builder.contains(args[0].clone(), args[1].clone())),
        "str.indexof" if args.len() == 3 => {
            Ok(builder.index_of(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.replace" if args.len() == 3 => {
            Ok(builder.replace(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.replace_all" if args.len() == 3 => {
            Ok(builder.replace_all(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.replace_re" if args.len() == 3 => {
            Ok(builder.replace_re(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.replace_re_all" if args.len() == 3 => {
            Ok(builder.replace_re_all(args[0].clone(), args[1].clone(), args[2].clone()))
        }
        "str.to_int" | "str.to_int" if args.len() == 1 => Ok(builder.to_int(args[0].clone())),
        "str.from_int" if args.len() == 1 => Ok(builder.from_int(args[0].clone())),

        // int
        "+" => Ok(builder.add(args)),
        "-" if args.len() == 1 => Ok(builder.neg(args[0].clone())),
        "-" if args.len() == 2 => Ok(builder.sub(args[0].clone(), args[1].clone())),
        "*" => Ok(builder.mul(args)),
        "div" if args.len() == 2 => Ok(builder.div(args[0].clone(), args[1].clone())),
        "mod" if args.len() == 2 => Ok(builder.mod_(args[0].clone(), args[1].clone())),
        "<" if args.len() == 2 => Ok(builder.lt(args[0].clone(), args[1].clone())),
        "<=" if args.len() == 2 => Ok(builder.le(args[0].clone(), args[1].clone())),
        ">" if args.len() == 2 => Ok(builder.gt(args[0].clone(), args[1].clone())),
        ">=" if args.len() == 2 => Ok(builder.ge(args[0].clone(), args[1].clone())),

        _ => Err(AstError::Unsupported(format!(
            "{} {}",
            name,
            args.iter().format(" ")
        ))),
    }
}

fn convert_sort(sort: &smt2parser::concrete::Sort) -> Result<Sort, AstError> {
    let err = Err(AstError::Unsupported(format!("{}", sort)));
    match sort {
        smt2parser::concrete::Sort::Simple { identifier } => match identifier {
            Identifier::Simple { symbol } => match symbol.0.as_str() {
                "Int" => Ok(Sort::Int),
                "Bool" => Ok(Sort::Bool),
                "String" => Ok(Sort::String),
                _ => err,
            },
            Identifier::Indexed { .. } => err,
        },
        smt2parser::concrete::Sort::Parameterized { .. } => err,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_smt_string_printable_ascii() {
        assert_eq!(parse_smtlib_string("A").unwrap(), "A");
        assert_eq!(parse_smtlib_string("Hello").unwrap(), "Hello");
        assert_eq!(parse_smtlib_string("12345").unwrap(), "12345");
        assert_eq!(parse_smtlib_string("!@#").unwrap(), "!@#");
    }

    #[test]
    fn test_parse_smt_string_non_printable_ascii() {
        assert_eq!(parse_smtlib_string("\\u000A").unwrap(), "\n");
        assert_eq!(parse_smtlib_string("\\u000D").unwrap(), "\r");
        assert_eq!(parse_smtlib_string("\\u0009").unwrap(), "\t");
    }

    #[test]
    fn test_parse_smt_string_non_ascii() {
        assert_eq!(parse_smtlib_string("\\u00A9").unwrap(), "©");
        assert_eq!(parse_smtlib_string("\\u20AC").unwrap(), "€");
        assert_eq!(parse_smtlib_string("\\u{1F600}").unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_unicode_escape() {
        assert_eq!(parse_smtlib_string("\\u{10348}").unwrap(), "𐍈");
        assert_eq!(parse_smtlib_string("\\u{1F600}").unwrap(), "😀");
    }

    #[test]
    fn test_parse_smt_string_unicode_invalid_smt() {
        assert!(parse_smtlib_string("\\u{3FFFF}").is_err());
    }

    #[test]
    fn test_parse_smt_string_mixed_string() {
        assert_eq!(parse_smtlib_string("A\\u000AB").unwrap(), "A\nB");
        assert_eq!(
            parse_smtlib_string("Hello\\u0020World").unwrap(),
            "Hello World"
        );
        assert_eq!(
            parse_smtlib_string("Line1\\u000ALine2").unwrap(),
            "Line1\nLine2"
        );
        assert_eq!(
            parse_smtlib_string("Tab\\u0009Space").unwrap(),
            "Tab\tSpace"
        );
        assert_eq!(
            parse_smtlib_string("Emoji\\u{1F600}Face").unwrap(),
            "Emoji😀Face"
        );
    }

    #[test]
    fn test_parse_smt_string_invalid_escape_sequence() {
        assert!(parse_smtlib_string("\\uXYZ").is_err());
        assert!(parse_smtlib_string("\\u{XYZ}").is_err());
        assert!(parse_smtlib_string("\\u{110000}").is_err()); // Invalid Unicode code point
    }
}
