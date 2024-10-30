use itertools::Itertools;
use smt2parser::visitors::TermVisitor;

use crate::{
    context::{Sort, Sorted},
    node::{Node, NodeKind},
    smt::{AstError, Constant, Identifier, Index, Keyword, SExpr, Symbol},
};

use super::ScriptBuilder;

impl<'a> TermVisitor<Constant, Identifier, Keyword, SExpr, Symbol, Sort> for ScriptBuilder<'a> {
    type T = Node;

    type E = AstError;

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        let expr = match constant {
            Constant::String(s) => self.mngr.const_string(s),
            Constant::Int(i) => self.mngr.int(i as i64),
            Constant::Real(_) => return Err(AstError::Unsupported("Real constant".to_string())),
        };
        Ok(expr)
    }

    fn visit_qual_identifier(&mut self, qual_identifier: Identifier) -> Result<Self::T, Self::E> {
        // If it is not an application or constant, it is a variable or 0-ary function (true or false)
        if qual_identifier.indices().is_empty() {
            let name = qual_identifier.symbol();
            match self.mngr.get_var(name) {
                Some(var) => match var.sort() {
                    Sort::Bool | Sort::Int | Sort::String => {
                        if let Some(v) = self.mngr.get_var(&name) {
                            Ok(self.mngr.var(v))
                        } else {
                            Err(AstError::Undeclared(name.clone()))
                        }
                    }
                    Sort::RegLan => todo!(),
                },
                None => match name.as_str() {
                    "true" => Ok(self.mngr.ttrue()),
                    "false" => Ok(self.mngr.ffalse()),
                    "re.all" => {
                        let re = self.mngr.re_builder().all();
                        Ok(self.mngr.create_node(NodeKind::Regex(re), vec![]))
                    }
                    "re.none" => {
                        let re = self.mngr.re_builder().none();
                        Ok(self.mngr.create_node(NodeKind::Regex(re), vec![]))
                    }
                    "re.allchar" => {
                        let re = self.mngr.re_builder().any_char();
                        Ok(self.mngr.create_node(NodeKind::Regex(re), vec![]))
                    }
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
        let expr: Node = match fname.symbol().as_str() {
            // Core
            "not" if args.len() == 1 => self.mngr.not(args.pop().unwrap()),
            "and" => self.mngr.and(args),
            "or" => self.mngr.or(args),
            "=>" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.imp(left, right)
            }
            "=" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.eq(left, right)
            }
            "ite" if args.len() == 3 => {
                let else_branch = args.pop().unwrap();
                let then_branch = args.pop().unwrap();
                let cond = args.pop().unwrap();
                self.mngr.ite(cond, then_branch, else_branch)
            }
            "distinct" => return Err(AstError::Unsupported("distinct".to_string())),
            // String
            "str.++" => self.mngr.concat(args),
            "str.len" if args.len() == 1 => self.mngr.str_len(args.pop().unwrap()),
            "str.substr" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.substr".to_string()))
            }
            "str.at" if args.len() == 2 => return Err(AstError::Unsupported("str.at".to_string())),
            "str.prefixof" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.prefix_of(left, right)
            }
            "str.suffixof" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.suffix_of(left, right)
            }
            "str.contains" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.contains(left, right)
            }
            "str.indexof" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.indexof".to_string()))
            }

            "str.replace" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.replace".to_string()))
            }
            "str.replace_all" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.replace_all".to_string()))
            }
            "str.replace_re" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.replace_re".to_string()))
            }
            "str.replace_re_all" if args.len() == 3 => {
                return Err(AstError::Unsupported("str.replace_re_all".to_string()))
            }
            "str.to_int" if args.len() == 1 => {
                return Err(AstError::Unsupported("str.to_int".to_string()))
            }
            "str.to.int" if args.len() == 1 && self.smt25 => {
                return Err(AstError::Unsupported("str.to.int".to_string()))
            }
            "str.from_int" if args.len() == 1 => {
                return Err(AstError::Unsupported("str.from_int".to_string()))
            }
            "str.from.int" if args.len() == 1 && self.smt25 => {
                return Err(AstError::Unsupported("str.from.int".to_string()))
            }
            // String regex
            "str.in_re" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.in_re(left, right)
            }
            "str.to_re" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                // Must be a string constant
                match arg.kind() {
                    NodeKind::String(s) => {
                        let re = self.mngr.re_builder().word(s.clone().into());
                        self.mngr.create_node(NodeKind::Regex(re), vec![])
                    }
                    _ => return Err(AstError::Unsupported("str.to_re".to_string())),
                }
            }
            "str.to.re" if args.len() == 1 && self.smt25 => {
                let arg = args.pop().unwrap();
                // Must be a string constant
                match arg.kind() {
                    NodeKind::String(s) => {
                        let re = self.mngr.re_builder().word(s.clone().into());
                        self.mngr.create_node(NodeKind::Regex(re), vec![])
                    }
                    _ => return Err(AstError::Unsupported("str.to_re".to_string())),
                }
            }
            "re.range" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                if let (NodeKind::String(left), NodeKind::String(right)) =
                    (left.kind(), right.kind())
                {
                    let re = if left.len() == 1 && right.len() == 1 {
                        self.mngr
                            .re_builder()
                            .range(left.chars().next().unwrap(), right.chars().next().unwrap())
                    } else {
                        self.mngr.re_builder().none()
                    };
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!(
                        "re.range {} {})",
                        left, right
                    )));
                }
            }
            "re.++" => {
                let mut re_args = vec![];
                for arg in args {
                    if let NodeKind::Regex(re) = arg.kind() {
                        re_args.push(re.clone());
                    } else {
                        return Err(AstError::Unsupported(format!("re.++ on {}", arg)));
                    }
                }
                let re = self.mngr.re_builder().concat(re_args);
                self.mngr.create_node(NodeKind::Regex(re), vec![])
            }
            "re.union" => {
                let mut re_args = vec![];
                for arg in args {
                    if let NodeKind::Regex(re) = arg.kind() {
                        re_args.push(re.clone());
                    } else {
                        return Err(AstError::Unsupported(format!("re.union on {}", arg)));
                    }
                }
                let re = self.mngr.re_builder().union(re_args);
                self.mngr.create_node(NodeKind::Regex(re), vec![])
            }
            "re.inter" => {
                let mut re_args = vec![];
                for arg in args {
                    if let NodeKind::Regex(re) = arg.kind() {
                        re_args.push(re.clone());
                    } else {
                        return Err(AstError::Unsupported(format!("re.inter on {}", arg)));
                    }
                }
                let re = self.mngr.re_builder().inter(re_args);
                self.mngr.create_node(NodeKind::Regex(re), vec![])
            }
            "re.*" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().star(re.clone());
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!("(re.* {})", arg)));
                }
            }
            "re.+" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().plus(re.clone());
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!("(re.+ {})", arg)));
                }
            }
            "re.opt" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().opt(re.clone());
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!("(re.opt {})", arg)));
                }
            }
            "re.comp" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().star(re.clone());
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!("(re.comp {})", arg)));
                }
            }
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

                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().loop_(re.clone(), lower, upper);
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!(
                        "(re.loop {} {} {})",
                        arg, lower, upper
                    )));
                }
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

                let arg = args.pop().unwrap();
                if let NodeKind::Regex(re) = arg.kind() {
                    let re = self.mngr.re_builder().pow(re.clone(), exp);
                    self.mngr.create_node(NodeKind::Regex(re), vec![])
                } else {
                    return Err(AstError::Unsupported(format!("(re.^ {} {})", arg, exp)));
                }
            }

            // int
            "+" => self.mngr.add(args),
            "-" if args.len() == 1 => {
                let arg = args.pop().unwrap();
                self.mngr.neg(arg)
            }
            "-" => self.mngr.sub(args),
            "*" => self.mngr.mul(args),
            "div" if args.len() == 2 => return Err(AstError::Unsupported("div".to_string())),
            "mod" if args.len() == 2 => return Err(AstError::Unsupported("mod".to_string())),
            "<" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.lt(left, right)
            }
            "<=" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.le(left, right)
            }
            ">" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.gt(left, right)
            }
            ">=" if args.len() == 2 => {
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                self.mngr.ge(left, right)
            }
            _ => {
                return Err(AstError::Unsupported(format!(
                    "{} {}",
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

    use crate::node::NodeManager;

    use super::*;

    fn parse_term(term: &str, mngr: &mut NodeManager) -> Node {
        let script = format!("(assert {})", term);
        let parser = ScriptBuilder::new(mngr);
        let script = parser.parse_script(script.as_bytes()).unwrap();
        match &script.commands()[0] {
            crate::smt::SmtCommand::AssertNew(node) => node.clone(),
            _ => unreachable!(),
        }
    }

    #[test]
    fn parse_re_all() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"re.all"#, &mut mngr);

        let all = mngr.re_builder().all();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(all), vec![]));
    }

    #[test]
    fn parse_re_none() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"re.none"#, &mut mngr);
        let none = mngr.re_builder().none();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(none), vec![]));
    }

    #[test]
    fn parse_re_allchar() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"re.allchar"#, &mut mngr);
        let allchar = mngr.re_builder().any_char();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(allchar), vec![]));
    }

    #[test]
    fn parse_re_plus() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"(re.+ (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().word("a".into());
        let plus = mngr.re_builder().plus(str_a);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(plus), vec![]));
    }

    #[test]
    fn parse_re_comp() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"(re.comp (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().word("a".into());
        let comp = mngr.re_builder().comp(str_a);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(comp), vec![]));
    }

    #[test]
    fn parse_re_loop() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"((_ re.loop 1 2) (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().word("a".into());
        let loop_ = mngr.re_builder().loop_(str_a, 1, 2);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(loop_), vec![]));
    }

    #[test]
    fn parse_re_pow() {
        let mut mngr = NodeManager::default();
        let term = parse_term(r#"((_ re.^ 2) (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().word("a".into());
        let pow = mngr.re_builder().pow(str_a, 2);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(pow), vec![]));
    }
}
