use std::rc::Rc;

use crate::node::error::NodeError;
use crate::node::Node;
use crate::node::NodeKind;
use crate::node::NodeManager;
use crate::node::Sort;
use crate::node::Sorted;
use crate::node::Variable;
use num_bigint::BigUint;
use num_traits::cast::ToPrimitive;

use smallvec::smallvec;
use smt2parser::concrete as smt;
use smt2parser::visitors::Index;
use smtlib_str::alphabet::CharRange;
use smtlib_str::SmtString;

use super::{AstError, Command};

pub struct Converter<'a> {
    mngr: &'a mut NodeManager,

    let_bindings: Vec<(smt::Symbol, smt::Term)>,
}

impl<'a> Converter<'a> {
    pub fn new(mngr: &'a mut NodeManager) -> Self {
        Self {
            mngr,
            let_bindings: vec![],
        }
    }

    /// Convert a SMT-LIB command to an internal command.
    pub fn convert(&mut self, cmd: smt::Command) -> Result<Command, AstError> {
        match cmd {
            smt::Command::Assert { term } => Ok(Command::Assert(self.term(term)?)),
            smt::Command::CheckSat => Ok(Command::CheckSat),
            smt::Command::DeclareConst { symbol, sort } => Ok(Command::DeclareConst(
                self.declare_const(symbol, sort)?.clone(),
            )),
            smt::Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                if parameters.is_empty() {
                    Ok(Command::DeclareConst(
                        self.declare_const(symbol, sort)?.clone(),
                    ))
                } else {
                    Err(AstError::Unsupported("declare-fun".to_string()))
                }
            }
            smt::Command::SetLogic { symbol } => {
                log::debug!("set-logic has no effect");
                Ok(Command::SetLogic(symbol.0))
            }
            smt::Command::Echo { message } => Ok(Command::Echo(message)),
            smt::Command::Exit => Ok(Command::Exit),

            smt::Command::GetModel => Ok(Command::GetModel),
            smt::Command::SetInfo { .. } | smt::Command::SetOption { .. } => {
                log::warn!("Ignoring {}", cmd);
                Ok(Command::NoOp)
            }
            _ => Err(AstError::Unsupported(cmd.to_string())),
        }
    }

    /// Declare a constant.
    /// This will add a new variable to the node manager with the given symbol and sort.
    fn declare_const(
        &mut self,
        symbol: smt::Symbol,
        sort: smt::Sort,
    ) -> Result<Rc<Variable>, AstError> {
        // todo: do we need to check if the symbol is escaped in | |?
        let symbol = symbol.0.clone();
        let sort = self.sort(sort)?;
        match self.mngr.new_var(symbol, sort) {
            Ok(v) => Ok(v),
            Err(NodeError::AlreadyDeclared(s, _, _)) => Err(AstError::AlreadyDeclared(s)),
            _ => unreachable!(),
        }
    }

    /// Convert a SMT-LIB sort to an internal sort.
    /// Sorts are indexed by a symbol:
    ///
    /// - "Bool": Boolean sort
    /// - "Int": Integer sort
    /// - "String": String sort
    ///
    /// All other sorts are unsupported.
    fn sort(&mut self, sort: smt::Sort) -> Result<Sort, AstError> {
        match sort {
            smt::Sort::Simple { identifier } => match identifier {
                smt::Identifier::Simple { symbol } => match symbol.0.as_str() {
                    "Bool" => Ok(Sort::Bool),
                    "Int" => Ok(Sort::Int),
                    "String" => Ok(Sort::String),
                    _ => Err(AstError::Unsupported(symbol.0.clone())),
                },
                smt::Identifier::Indexed { .. } => {
                    Err(AstError::Unsupported(identifier.to_string()))
                }
            },
            smt::Sort::Parameterized { .. } => Err(AstError::Unsupported(sort.to_string())),
        }
    }

    /// Convert a SMT-LIB term to an internal node.
    fn term(&mut self, term: smt::Term) -> Result<Node, AstError> {
        match term {
            smt::Term::Constant(c) => self.constant(c),
            smt::Term::QualIdentifier(qa) => self.qual_identifier(qa),
            smt::Term::Application {
                qual_identifier,
                arguments,
            } => self.application(qual_identifier, arguments),
            smt::Term::Let { var_bindings, term } => {
                // push the current let bindings to the stack
                let n = self.let_bindings.len();
                self.let_bindings.extend(var_bindings);
                let term = self.term(*term)?;
                // Remove the let bindings from the stack
                for _ in 0..n {
                    self.let_bindings.pop();
                }

                Ok(term)
            }
            smt::Term::Forall { .. }
            | smt::Term::Exists { .. }
            | smt::Term::Match { .. }
            | smt::Term::Attributes { .. } => Err(AstError::Unsupported(term.to_string())),
        }
    }

    fn constant(&mut self, constant: smt::Constant) -> Result<Node, AstError> {
        match &constant {
            smt::Constant::Numeral(num) => {
                let conv = self.numeral(num)?;
                Ok(self.mngr.const_int(conv as i64))
            }
            smt::Constant::String(s) => {
                let parsed = SmtString::parse(s);
                Ok(self.mngr.const_string(parsed))
            }
            smt::Constant::Decimal(_)
            | smt::Constant::Hexadecimal(_)
            | smt::Constant::Binary(_) => Err(AstError::Unsupported(constant.to_string())),
        }
    }

    fn numeral(&mut self, num: &BigUint) -> Result<u32, AstError> {
        match num.to_u32() {
            Some(i) => Ok(i),
            None => Err(AstError::NumeralOutOfBounds(num.clone())),
        }
    }

    /// Convert a SMT-LIB qualified identifier to an internal node.
    /// This will convert the identifier to a variable or let binding or constant.
    fn qual_identifier(&mut self, qi: smt::QualIdentifier) -> Result<Node, AstError> {
        match &qi {
            smt::QualIdentifier::Simple { identifier } => match identifier {
                smt::Identifier::Simple { symbol } => {
                    // check if it is a let binding
                    // check from right to left to get the last binding for the symbol
                    for (sym, term) in self.let_bindings.iter().rev() {
                        if sym.0 == symbol.0 {
                            return self.term(term.clone());
                        }
                    }

                    // check if it is a variable
                    if let Some(v) = self.mngr.get_var(symbol.0.as_str()) {
                        return Ok(self.mngr.var(v));
                    }
                    // check if it is a constant
                    match symbol.0.as_str() {
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
                        _ => Err(AstError::Undeclared(symbol.0.clone())),
                    }
                }
                smt::Identifier::Indexed { .. } => Err(AstError::Unsupported(qi.to_string())),
            },
            smt::QualIdentifier::Sorted { .. } => Err(AstError::Unsupported(qi.to_string())),
        }
    }

    fn application(
        &mut self,
        fun: smt::QualIdentifier,
        arguments: Vec<smt::Term>,
    ) -> Result<Node, AstError> {
        let mut args = Vec::with_capacity(arguments.len());
        for arg in arguments {
            args.push(self.term(arg)?);
        }
        let app = match &fun {
            smt::QualIdentifier::Simple { identifier } => match identifier {
                smt::Identifier::Simple { symbol } => match symbol.0.as_str() {
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
                        if right.sort() == left.sort() {
                            if right.sort().is_bool() {
                                self.mngr.equiv(left, right)
                            } else {
                                self.mngr.eq(left, right)
                            }
                        } else {
                            return Err(AstError::Unsupported(format!("= {} {}", left, right)));
                        }
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
                        let len = args.pop().unwrap();
                        let idx = args.pop().unwrap();
                        let s = args.pop().unwrap();
                        self.mngr.substr(s, idx, len)
                    }
                    "str.at" if args.len() == 2 => {
                        let idx = args.pop().unwrap();
                        let s = args.pop().unwrap();
                        self.mngr.at(s, idx)
                    }
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
                    "str.to_int" if args.len() == 1 => {
                        let arg = args.pop().unwrap();
                        self.mngr.str_to_int(arg)
                    }
                    "str.from_int" if args.len() == 1 => {
                        let arg = args.pop().unwrap();
                        self.mngr.str_from_int(arg)
                    }
                    "str.replace" if args.len() == 3 => {
                        let to = args.pop().unwrap();
                        let from = args.pop().unwrap();
                        let s = args.pop().unwrap();
                        self.mngr.str_replace(s, from, to)
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
                    "str.from_int" if args.len() == 1 => {
                        return Err(AstError::Unsupported("str.from_int".to_string()))
                    }
                    // String regex
                    "str.in_re" if args.len() == 2 => {
                        let right = args.pop().unwrap();
                        let left = args.pop().unwrap();
                        self.mngr.in_re(left, right)
                    }
                    "str.in_re" => {
                        panic!("str.in_re requires two arguments but got {}", args.len())
                    }
                    "str.to_re" if args.len() == 1 => {
                        let arg = args.pop().unwrap();
                        // Must be a string constant
                        match arg.kind() {
                            NodeKind::String(s) => {
                                let re = self.mngr.re_builder().to_re(s.clone());
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
                                let l = left[0];
                                let r = right[0];
                                let range = CharRange::new(l, r);
                                self.mngr.re_builder().range(range)
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
                        let mut re_args = smallvec![];
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
                        let mut re_args = smallvec![];
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
                        let mut re_args = smallvec![];
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
                            let re = self.mngr.re_builder().comp(re.clone());
                            self.mngr.create_node(NodeKind::Regex(re), vec![])
                        } else {
                            return Err(AstError::Unsupported(format!("(re.comp {})", arg)));
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
                    "div" if args.len() == 2 => {
                        return Err(AstError::Unsupported("div".to_string()))
                    }
                    "mod" if args.len() == 2 => {
                        return Err(AstError::Unsupported("mod".to_string()))
                    }
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
                            "Unsupported function: {}",
                            fun
                        )))
                    }
                },
                smt::Identifier::Indexed { symbol, indices } => match symbol.0.as_str() {
                    "re.loop" if indices.len() == 2 && args.len() == 1 => {
                        let (lower, upper) = if let (Index::Numeral(n1), Index::Numeral(n2)) =
                            (indices[0].clone(), indices[1].clone())
                        {
                            (self.numeral(&n1)?, self.numeral(&n2)?)
                        } else {
                            return Err(AstError::Undeclared(format!(
                                "Invalid loop bounds: {}, {}",
                                indices[0], indices[1]
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
                    "re.^" if indices.len() == 1 && args.len() == 1 => {
                        let exp = if let Index::Numeral(e) = &indices[0] {
                            self.numeral(e)?
                        } else {
                            return Err(AstError::Unsupported(format!(
                                "Invalid exponent for re.^: {}",
                                indices[0]
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
                    _ => {
                        return Err(AstError::Unsupported(format!(
                            "Unsupported function: {}",
                            fun
                        )))
                    }
                },
            },
            smt::QualIdentifier::Sorted { .. } => {
                return Err(AstError::Unsupported(fun.to_string()))
            }
        };
        Ok(app)
    }
}

#[cfg(test)]
mod tests {

    use smt2parser::concrete::SyntaxBuilder;
    use smtlib_str::SmtString;

    use crate::{node::NodeManager, smt::Script};

    use super::*;

    fn convert_term(term: &str, mngr: &mut NodeManager) -> Node {
        let script = format!("(assert {})", term);
        let cmds = smt2parser::CommandStream::new(script.as_bytes(), SyntaxBuilder, None);
        let mut converter = Converter::new(mngr);
        let mut script = Script::default();
        for cmd in cmds {
            script.push(converter.convert(cmd.unwrap()).unwrap());
        }

        match &script.commands()[0] {
            crate::smt::Command::Assert(node) => node.clone(),
            _ => unreachable!(),
        }
    }

    #[test]
    fn parse_re_all() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"re.all"#, &mut mngr);

        let all = mngr.re_builder().all();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(all), vec![]));
    }

    #[test]
    fn parse_re_none() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"re.none"#, &mut mngr);
        let none = mngr.re_builder().none();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(none), vec![]));
    }

    #[test]
    fn parse_re_allchar() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"re.allchar"#, &mut mngr);
        let allchar = mngr.re_builder().any_char();
        assert_eq!(term, mngr.create_node(NodeKind::Regex(allchar), vec![]));
    }

    #[test]
    fn parse_re_plus() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"(re.+ (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().to_re("a".into());
        let plus = mngr.re_builder().plus(str_a);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(plus), vec![]));
    }

    #[test]
    fn parse_re_comp() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"(re.comp (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().to_re("a".into());
        let comp = mngr.re_builder().comp(str_a);
        let expected = mngr.create_node(NodeKind::Regex(comp), vec![]);
        assert_eq!(term, expected, "\nExpected: {}\nGot: {}", expected, term);
    }

    #[test]
    fn parse_re_loop() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"((_ re.loop 1 2) (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().to_re("a".into());
        let loop_ = mngr.re_builder().loop_(str_a, 1, 2);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(loop_), vec![]));
    }

    #[test]
    fn parse_re_pow() {
        let mut mngr = NodeManager::default();
        let term = convert_term(r#"((_ re.^ 2) (str.to_re "a"))"#, &mut mngr);
        let str_a = mngr.re_builder().to_re("a".into());
        let pow = mngr.re_builder().pow(str_a, 2);
        assert_eq!(term, mngr.create_node(NodeKind::Regex(pow), vec![]));
    }

    #[test]
    fn parse_let() {
        let mut mngr = NodeManager::default();
        let x = mngr.new_var("x".to_string(), Sort::String).unwrap();
        let term = convert_term(r#"(let ((y "")) (= x y))"#, &mut mngr);

        let vx = mngr.var(x);
        let epsi = mngr.const_string(SmtString::empty());
        let expected = mngr.eq(vx, epsi);
        assert_eq!(term, expected);
    }
}
