use std::rc::Rc;

use crate::context::Context;

use super::AstError;
use super::{
    expr::{ExprType, Expression, StrExpr},
    script::Script,
    smt_max_char,
};
use crate::repr::{Sort, Variable};

use itertools::Itertools;

use num_traits::cast::ToPrimitive;
use regulaer::re::{ReBuilder, Regex};
use smt2parser::visitors::Index;
use smt2parser::{
    concrete::{Command, Constant, QualIdentifier, SyntaxBuilder, Term},
    visitors::Identifier,
    CommandStream,
};

pub struct AstParser {
    smt25: bool,
}
impl Default for AstParser {
    fn default() -> Self {
        Self { smt25: false }
    }
}

enum IdentifierType {
    Var(Rc<Variable>),
    ConstFun(String),
}

impl AstParser {
    pub fn parse_script(
        &self,
        input: impl std::io::BufRead,
        ctx: &mut Context,
    ) -> Result<Script, AstError> {
        let cmds = CommandStream::new(input, SyntaxBuilder, None);
        let mut script = Script::default();
        let cmds = cmds.collect::<Result<Vec<_>, _>>()?;
        for cmd in cmds {
            match cmd {
                Command::Assert { term } => {
                    let expr = self.convert_term(&term, ctx)?;
                    script.assert(expr);
                }
                Command::CheckSat => script.check_sat(),
                Command::DeclareConst { symbol, sort } => {
                    let sort = self.convert_sort(&sort)?;
                    let var = ctx
                        .make_var(symbol.0.to_owned(), sort)
                        .ok_or(AstError::Unsupported(format!("{}", symbol)))?;
                    script.declare_var(var);
                }
                Command::DeclareFun {
                    symbol,
                    parameters,
                    sort,
                } if parameters.is_empty() => {
                    let sort = self.convert_sort(&sort)?;
                    let var = ctx
                        .make_var(symbol.0.to_owned(), sort)
                        .ok_or(AstError::Unsupported(format!("{}", symbol)))?;
                    script.declare_var(var);
                }
                Command::Echo { .. } => {}
                Command::Exit => script.exit(),
                Command::GetModel => script.get_model(),
                Command::SetLogic { symbol } => script.set_logic(symbol.0.to_owned()),
                Command::SetOption { keyword, value } => {
                    log::warn!("Ignoring set-option! {}: {}", keyword, value)
                }
                Command::SetInfo { keyword, value } => {
                    log::warn!("Ignoring set-info! {}: {}", keyword, value)
                }
                _ => return Err(AstError::Unsupported(format!("{}", cmd))),
            }
        }

        Ok(script)
    }

    fn convert_term(&self, term: &Term, ctx: &mut Context) -> Result<Rc<Expression>, AstError> {
        match term {
            Term::Constant(c) => match c {
                Constant::String(s) => {
                    let parsed = self.parse_smtlib_string(s)?;
                    Ok(ctx.ast_builder().string(parsed))
                }
                Constant::Numeral(n) => n
                    .to_isize()
                    .map(|n| ctx.ast_builder().int(n))
                    .ok_or(AstError::Unsupported(format!("{}", n))),
                _ => Err(AstError::Unsupported(format!("{}", c))),
            },
            Term::QualIdentifier(i) => {
                let iden = self.convert_identifier(i, ctx)?;
                match iden {
                    IdentifierType::Var(v) => Ok(ctx.ast_builder().var(v)),
                    IdentifierType::ConstFun(fname) => match fname.as_str() {
                        "true" => Ok(ctx.ast_builder().bool(true)),
                        "false" => Ok(ctx.ast_builder().bool(false)),
                        _ => Err(AstError::Undeclared(fname)),
                    },
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => self.convert_application(qual_identifier, arguments, ctx),
            _ => Err(AstError::Unsupported(format!("{}", term))),
        }
    }

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

    fn convert_identifier(
        &self,
        identifier: &QualIdentifier,
        ctx: &mut Context,
    ) -> Result<IdentifierType, AstError> {
        let identifier = match identifier {
            QualIdentifier::Simple { identifier } => identifier,
            QualIdentifier::Sorted { identifier, .. } => identifier,
        };
        match identifier {
            Identifier::Simple { symbol } => {
                let name = symbol.0.to_owned();
                if let Some(var) = ctx.get_var(&name) {
                    Ok(IdentifierType::Var(var))
                } else {
                    Ok(IdentifierType::ConstFun(name))
                }
            }
            Identifier::Indexed { .. } => Err(AstError::Unsupported(identifier.to_string())),
        }
    }

    fn convert_application(
        &self,
        qual_identifier: &QualIdentifier,
        arguments: &[Term],
        ctx: &mut Context,
    ) -> Result<Rc<Expression>, AstError> {
        let identifier = match qual_identifier {
            QualIdentifier::Simple { identifier } => identifier,
            QualIdentifier::Sorted { identifier, .. } => identifier,
        };

        match identifier {
            Identifier::Simple { symbol } => {
                if symbol.0 == "str.in_re" || symbol.0 == "str.in.re" {
                    assert!(arguments.len() == 2);
                    let pat = self.convert_term(&arguments[0], ctx)?;
                    let re = self.convert_re(ctx, &arguments[1])?;
                    let re = ctx.ast_builder().regex(re);
                    Ok(ctx.ast_builder().in_re(pat, re))
                } else {
                    let args = arguments
                        .iter()
                        .map(|arg| self.convert_term(arg, ctx))
                        .collect::<Result<Vec<_>, _>>()?;
                    self.smt2expr(&symbol.0, args, ctx)
                }
            }
            Identifier::Indexed { .. } => Err(AstError::Unsupported(identifier.to_string())),
        }
    }

    fn convert_re(&self, ctx: &mut Context, term: &Term) -> Result<Regex, AstError> {
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
                        let s_term = self.convert_term(&arguments[0], ctx)?;
                        let s = if let ExprType::String(StrExpr::Constant(s)) = s_term.get_type() {
                            s
                        } else {
                            return Err(AstError::Unsupported(format!(
                                "Regex string '{}'",
                                arguments[0]
                            )));
                        };
                        Ok(ctx.ast_builder().re_builder().word(s.clone().into()))
                    }
                    "re.range" => {
                        assert!(arguments.len() == 2);
                        let s_term = self.convert_term(&arguments[0], ctx)?;
                        let start =
                            if let ExprType::String(StrExpr::Constant(s)) = s_term.get_type() {
                                s
                            } else {
                                return Err(AstError::Unsupported(format!(
                                    "Regex range start '{}'",
                                    arguments[0]
                                )));
                            };
                        let e_term = self.convert_term(&arguments[1], ctx)?;
                        let end = if let ExprType::String(StrExpr::Constant(s)) = e_term.get_type()
                        {
                            s
                        } else {
                            return Err(AstError::Unsupported(format!(
                                "Regex range end '{}'",
                                arguments[1]
                            )));
                        };
                        if start.len() != 1 || end.len() != 1 {
                            Ok(ctx.ast_builder().re_builder().none())
                        } else {
                            Ok(ctx
                                .ast_builder()
                                .re_builder()
                                .range(start.chars().next().unwrap(), end.chars().next().unwrap()))
                        }
                    }
                    "re.++" => {
                        let args = arguments
                            .iter()
                            .map(|arg| self.convert_re(ctx, arg))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(ctx.ast_builder().re_builder().concat(args))
                    }
                    "re.union" => {
                        let args = arguments
                            .iter()
                            .map(|arg| self.convert_re(ctx, arg))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(ctx.ast_builder().re_builder().union(args))
                    }
                    "re.inter" => {
                        let args = arguments
                            .iter()
                            .map(|arg| self.convert_re(ctx, arg))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(ctx.ast_builder().re_builder().inter(args))
                    }
                    "re.*" if arguments.len() == 1 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
                        Ok(ctx.ast_builder().re_builder().star(arg))
                    }
                    "re.+" if arguments.len() == 1 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
                        Ok(ctx.ast_builder().re_builder().plus(arg))
                    }
                    "re.opt" if arguments.len() == 1 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
                        Ok(ctx.ast_builder().re_builder().opt(arg))
                    }
                    "re.comp" if arguments.len() == 1 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
                        Ok(ctx.ast_builder().re_builder().comp(arg))
                    }
                    "re.loop" if arguments.len() == 1 && indices.len() == 2 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
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

                        Ok(ctx.ast_builder().re_builder().loop_(arg, lower, upper))
                    }
                    "re.^" if arguments.len() == 1 && indices.len() == 1 => {
                        let arg = self.convert_re(ctx, &arguments[0])?;
                        let n = if let Index::Numeral(n) = &indices[0] {
                            n.to_usize()
                                .ok_or(AstError::Unsupported(format!("{}", n)))?
                        } else {
                            return Err(AstError::Unsupported(format!("{:?}", indices[0])));
                        };

                        Ok(ctx.ast_builder().re_builder().pow(arg, n))
                    }

                    _ => Err(AstError::Unsupported(term.to_string())),
                }
            }
            Term::QualIdentifier(QualIdentifier::Simple { identifier }) => match identifier {
                Identifier::Simple { symbol } => match symbol.0.as_str() {
                    "re.all" => Ok(ctx.ast_builder().re_builder().all()),
                    "re.none" => Ok(ctx.ast_builder().re_builder().none()),
                    "re.allchar" => Ok(ctx.ast_builder().re_builder().any_char()),
                    _ => Err(AstError::Unsupported(format!("{}", symbol))),
                },
                Identifier::Indexed { .. } => Err(AstError::Unsupported(format!("{:?}", term))),
            },
            _ => Err(AstError::Unsupported(format!("{:?}", term))),
        }
    }

    fn smt2expr(
        &self,
        name: &str,
        args: Vec<Rc<Expression>>,
        ctx: &mut Context,
    ) -> Result<Rc<Expression>, AstError> {
        match name {
            // Core
            "not" if args.len() == 1 => Ok(ctx.ast_builder().not(args[0].clone())),
            "and" => Ok(ctx.ast_builder().and(args)),
            "or" => Ok(ctx.ast_builder().or(args)),
            "=>" if args.len() == 2 => Ok(ctx.ast_builder().imp(args[0].clone(), args[1].clone())),
            "=" if args.len() == 2 => Ok(ctx.ast_builder().eq(args[0].clone(), args[1].clone())),
            "ite" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .ite(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "distinct" => Ok(ctx.ast_builder().distinct(args)),
            // String
            "str.++" => Ok(ctx.ast_builder().concat(args)),
            "str.len" if args.len() == 1 => Ok(ctx.ast_builder().length(args[0].clone())),
            "str.substr" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .substr(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "str.at" if args.len() == 2 => {
                Ok(ctx.ast_builder().str_at(args[0].clone(), args[1].clone()))
            }
            "str.prefixof" if args.len() == 2 => Ok(ctx
                .ast_builder()
                .prefix_of(args[0].clone(), args[1].clone())),
            "str.suffixof" if args.len() == 2 => Ok(ctx
                .ast_builder()
                .suffix_of(args[0].clone(), args[1].clone())),
            "str.contains" if args.len() == 2 => {
                Ok(ctx.ast_builder().contains(args[0].clone(), args[1].clone()))
            }
            "str.indexof" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .index_of(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "str.replace" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .replace(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "str.replace_all" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .replace_all(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "str.replace_re" if args.len() == 3 => {
                Ok(ctx
                    .ast_builder()
                    .replace_re(args[0].clone(), args[1].clone(), args[2].clone()))
            }
            "str.replace_re_all" if args.len() == 3 => Ok(ctx.ast_builder().replace_re_all(
                args[0].clone(),
                args[1].clone(),
                args[2].clone(),
            )),
            "str.to_int" | "str.to_int" if args.len() == 1 => {
                Ok(ctx.ast_builder().to_int(args[0].clone()))
            }
            "str.from_int" if args.len() == 1 => Ok(ctx.ast_builder().from_int(args[0].clone())),

            // int
            "+" => Ok(ctx.ast_builder().add(args)),
            "-" if args.len() == 1 => Ok(ctx.ast_builder().neg(args[0].clone())),
            "-" if args.len() == 2 => Ok(ctx.ast_builder().sub(args[0].clone(), args[1].clone())),
            "*" => Ok(ctx.ast_builder().mul(args)),
            "div" if args.len() == 2 => Ok(ctx.ast_builder().div(args[0].clone(), args[1].clone())),
            "mod" if args.len() == 2 => {
                Ok(ctx.ast_builder().mod_(args[0].clone(), args[1].clone()))
            }
            "<" if args.len() == 2 => Ok(ctx.ast_builder().lt(args[0].clone(), args[1].clone())),
            "<=" if args.len() == 2 => Ok(ctx.ast_builder().le(args[0].clone(), args[1].clone())),
            ">" if args.len() == 2 => Ok(ctx.ast_builder().gt(args[0].clone(), args[1].clone())),
            ">=" if args.len() == 2 => Ok(ctx.ast_builder().ge(args[0].clone(), args[1].clone())),

            _ => Err(AstError::Unsupported(format!(
                "{} {}",
                name,
                args.iter().format(" ")
            ))),
        }
    }

    fn convert_sort(&self, sort: &smt2parser::concrete::Sort) -> Result<Sort, AstError> {
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
