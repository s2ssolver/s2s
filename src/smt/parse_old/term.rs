use itertools::Itertools;
use smt2parser::visitors::TermVisitor;

use crate::smt::{
    AstError, Constant, CoreExpr, Expression, Identifier, Index, IntExpr, Keyword, SExpr, Sort,
    StrExpr, Symbol,
};

use super::AstParser;

impl TermVisitor<Constant, Identifier, Keyword, SExpr, Symbol, Sort> for AstParser {
    type T = Expression;

    type E = AstError;

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        let expr = match constant {
            Constant::String(s) => StrExpr::Constant(s).into(),
            Constant::Int(i) => IntExpr::Constant(i).into(),
            Constant::Real(_) => return Err(AstError::Unsupported("Real constant".to_string())),
        };
        Ok(expr)
    }

    fn visit_qual_identifier(&mut self, qual_identifier: Identifier) -> Result<Self::T, Self::E> {
        // If it is not an application or constant, it is a variable or 0-ary function (true or false)
        if qual_identifier.indices().is_empty() {
            let name = qual_identifier.symbol();
            match self.declared_vars.get(name) {
                Some(sort) => match sort {
                    Sort::Bool => Ok(CoreExpr::Var(name.clone()).into()),
                    Sort::Int => Ok(IntExpr::Var(name.clone()).into()),
                    Sort::String => Ok(StrExpr::Var(name.clone()).into()),
                    Sort::RegLan => todo!(),
                },
                None => match name.as_str() {
                    "true" => Ok(CoreExpr::Bool(true).into()),
                    "false" => Ok(CoreExpr::Bool(false).into()),
                    "re.all" => Ok(StrExpr::ReAll.into()),
                    "re.none" => Ok(StrExpr::ReNone.into()),
                    "re.allchar" => Ok(StrExpr::ReAllChar.into()),
                    _ => Err(AstError::Undeclared(name.clone())),
                },
            }
        } else {
            Err(AstError::Unsupported(format!(
                "Qualified identifier: {}",
                qual_identifier
            )))
        }
    }

    fn visit_application(
        &mut self,
        fname: Identifier,
        mut args: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        let expr: Expression = match fname.symbol().as_str() {
            // Core
            "not" if args.len() == 1 => CoreExpr::Not(std::mem::take(&mut args[0])).into(),
            "and" => CoreExpr::And(args).into(),
            "or" => CoreExpr::Or(args).into(),
            "=>" if args.len() == 2 => {
                CoreExpr::Imp(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "=" if args.len() == 2 => {
                CoreExpr::Equal(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "ite" if args.len() == 3 => CoreExpr::Ite(
                std::mem::take(&mut std::mem::take(&mut args[0])),
                std::mem::take(&mut std::mem::take(&mut args[1])),
                std::mem::take(&mut std::mem::take(&mut args[2])),
            )
            .into(),
            "distinct" => CoreExpr::Distinct(args).into(),
            // String
            "str.++" => StrExpr::Concat(args).into(),
            "str.len" if args.len() == 1 => StrExpr::Length(std::mem::take(&mut args[0])).into(),
            "str.substr" if args.len() == 3 => StrExpr::Substr(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.at" if args.len() == 2 => {
                StrExpr::At(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "str.prefixof" if args.len() == 2 => {
                StrExpr::PrefixOf(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "str.suffixof" if args.len() == 2 => {
                StrExpr::SuffixOf(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "str.contains" if args.len() == 2 => {
                StrExpr::Contains(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "str.indexof" if args.len() == 3 => StrExpr::IndexOf(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.replace" if args.len() == 3 => StrExpr::Replace(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.replace_all" if args.len() == 3 => StrExpr::ReplaceAll(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.replace_re" if args.len() == 3 => StrExpr::ReplaceRe(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.replace_re_all" if args.len() == 3 => StrExpr::ReplaceReAll(
                std::mem::take(&mut args[0]),
                std::mem::take(&mut args[1]),
                std::mem::take(&mut args[2]),
            )
            .into(),
            "str.to_int" if args.len() == 1 => StrExpr::ToInt(std::mem::take(&mut args[0])).into(),
            "str.to.int" if args.len() == 1 && self.smt25 => {
                StrExpr::ToInt(std::mem::take(&mut args[0])).into()
            }
            "str.from_int" if args.len() == 1 => {
                StrExpr::FromInt(std::mem::take(&mut args[0])).into()
            }
            "str.from.int" if args.len() == 1 && self.smt25 => {
                StrExpr::FromInt(std::mem::take(&mut args[0])).into()
            }
            // String regex
            "str.in_re" if args.len() == 2 => {
                StrExpr::InRe(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "str.to_re" if args.len() == 1 => StrExpr::ToRe(std::mem::take(&mut args[0])).into(),
            "str.to.re" if args.len() == 1 && self.smt25 => {
                StrExpr::ToRe(std::mem::take(&mut args[0])).into()
            }
            "re.range" if args.len() == 2 => {
                StrExpr::ReRange(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "re.++" => StrExpr::ReConcat(args).into(),
            "re.union" => StrExpr::ReUnion(args).into(),
            "re.inter" => StrExpr::ReInter(args).into(),
            "re.*" if args.len() == 1 => StrExpr::ReStar(std::mem::take(&mut args[0])).into(),
            "re.+" if args.len() == 1 => StrExpr::RePlus(std::mem::take(&mut args[0])).into(),
            "re.opt" if args.len() == 1 => StrExpr::ReOpt(std::mem::take(&mut args[0])).into(),
            "re.comp" if args.len() == 1 => StrExpr::ReComp(std::mem::take(&mut args[0])).into(),
            "re.loop" if fname.indices().len() == 2 && args.len() == 1 => {
                let (lower, upper) = if let (Index::Num(l), Index::Num(u)) =
                    (fname.indices()[0].clone(), fname.indices()[1].clone())
                {
                    (l, u)
                } else {
                    return Err(AstError::Unsupported(format!(
                        "Invalid lower bound for re.loop: {} {}",
                        fname.indices()[0],
                        fname.indices()[1]
                    )));
                };
                StrExpr::ReLoop(std::mem::take(&mut args[0]), lower, upper).into()
            }
            "re.^" if fname.indices().len() == 1 && args.len() == 1 => {
                let exp = if let Index::Num(e) = fname.indices()[0] {
                    e
                } else {
                    return Err(AstError::Unsupported(format!(
                        "Invalid exponent for re.^: {}",
                        fname.indices()[0]
                    )));
                };
                StrExpr::RePow(std::mem::take(&mut args[0]), exp).into()
            }

            // int
            "+" => IntExpr::Add(args).into(),
            "-" if args.len() == 1 => IntExpr::Neg(std::mem::take(&mut args[0])).into(),
            "-" if args.len() == 2 => {
                IntExpr::Sub(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "*" => IntExpr::Mul(args).into(),
            "div" if args.len() == 2 => {
                IntExpr::Div(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "mod" if args.len() == 2 => {
                IntExpr::Mod(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "<" if args.len() == 2 => {
                IntExpr::Lt(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            "<=" if args.len() == 2 => {
                IntExpr::Leq(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            ">" if args.len() == 2 => {
                IntExpr::Gt(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            ">=" if args.len() == 2 => {
                IntExpr::Geq(std::mem::take(&mut args[0]), std::mem::take(&mut args[1])).into()
            }
            _ => {
                return Err(AstError::Unsupported(format!(
                    "{:?} {}",
                    fname,
                    args.iter().format(" ")
                )))
            }
        };
        Ok(expr)
    }

    fn visit_let(
        &mut self,
        _var_bindings: Vec<(Symbol, Self::T)>,
        _term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("let".to_string()))
    }

    fn visit_forall(
        &mut self,
        _vars: Vec<(Symbol, Sort)>,
        _term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("forall".to_string()))
    }

    fn visit_exists(
        &mut self,
        _vars: Vec<(Symbol, Sort)>,
        _term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("exists".to_string()))
    }

    fn visit_match(
        &mut self,
        _term: Self::T,
        _cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("match".to_string()))
    }

    fn visit_attributes(
        &mut self,
        _term: Self::T,
        _attributes: Vec<(
            Keyword,
            smt2parser::visitors::AttributeValue<Constant, Symbol, SExpr>,
        )>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported("attributes".to_string()))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn parse_term(term: &str) -> Expression {
        let script = format!("(assert {})", term);

        let parser = AstParser::default();
        let script = parser.parse_script(script.as_bytes()).unwrap();
        match &script.commands()[0] {
            crate::smt::SmtCommand::Assert(expression) => expression.clone(),
            _ => unreachable!(),
        }
    }

    #[test]
    fn parse_re_all() {
        let term = parse_term(r#"re.all"#);
        assert_eq!(term, StrExpr::ReAll.into());
    }

    #[test]
    fn parse_re_none() {
        let term = parse_term(r#"re.none"#);
        assert_eq!(term, StrExpr::ReNone.into());
    }

    #[test]
    fn parse_re_allchar() {
        let term = parse_term(r#"re.allchar"#);
        assert_eq!(term, StrExpr::ReAllChar.into());
    }

    #[test]
    fn parse_re_plus() {
        let term = parse_term(r#"(re.+ (str.to_re "a"))"#);
        if let Expression::String(expr) = term {
            assert!(matches!(*expr, StrExpr::RePlus(_)));
        } else {
            panic!("Expected a re.+ expression");
        }
    }

    #[test]
    fn parse_re_comp() {
        let term = parse_term(r#"(re.comp (str.to_re "a"))"#);
        if let Expression::String(expr) = term {
            assert!(matches!(*expr, StrExpr::ReComp(_)));
        } else {
            panic!("Expected a re.+ expression");
        }
    }

    #[test]
    fn parse_re_loop() {
        let term = parse_term(r#"((_ re.loop 1 2) (str.to_re "a"))"#);
        if let Expression::String(expr) = term {
            assert!(matches!(*expr, StrExpr::ReLoop(_, 1, 2)));
        } else {
            panic!("Expected a re.loop expression");
        }
    }

    #[test]
    fn parse_re_pow() {
        let term = parse_term(r#"((_ re.^ 2) (str.to_re "a"))"#);
        if let Expression::String(expr) = term {
            assert!(matches!(*expr, StrExpr::RePow(_, 2)), "{}", expr);
        } else {
            panic!("Expected a re.loop expression");
        }
    }
}
