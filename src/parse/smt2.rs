use std::io::BufRead;

use aws_smt_ir::{
    logic::{all, ArithOp, StringOp, ALL},
    visit::{ControlFlow, SuperVisit, Visit, Visitor},
    Ctx, ISort, Script, Sorted, Term,
};

use crate::{
    formula::{Atom, Formula, Predicate},
    model::{
        linears::{IntArithTerm, LinearArithTerm, LinearConstraint, LinearConstraintType},
        words::{Pattern, WordEquation},
        Sort, VarManager,
    },
};

use super::{Instance, ParseError};

pub fn parse_smt<R: BufRead>(smt: R) -> Result<Instance, ParseError> {
    let script = Script::<Term>::parse(smt)
        .map_err(|e| ParseError::Other(format!("Error parsing SMT-LIB script: {}", e), None))?;
    let mut var_manager = VarManager::new();
    let mut asserts = vec![];
    for command in script {
        match command {
            smt2parser::concrete::Command::Assert { term } => {
                let mut visitor = FormulaBuilder {
                    var_manager: &var_manager,
                    context: Ctx::default(),
                };
                match term.visit_with(&mut visitor) {
                    ControlFlow::Continue(_) => unreachable!(),
                    ControlFlow::Break(res) => asserts.push(res?),
                }
            }
            smt2parser::concrete::Command::DeclareConst { symbol, sort } => {
                let _v = var_manager.new_var(&symbol.0, isort2sort(&sort)?);
            }
            smt2parser::concrete::Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                if parameters.is_empty() {
                    // This is a constant function, i.e., a variable
                    var_manager.new_var(&symbol.0, isort2sort(&sort)?);
                } else {
                    return Err(ParseError::Unsupported(
                        "Non-constant function declaration".to_string(),
                    ));
                }
            }
            smt2parser::concrete::Command::CheckSat
            | smt2parser::concrete::Command::SetLogic { .. }
            | smt2parser::concrete::Command::GetModel => {}

            smt2parser::concrete::Command::CheckSatAssuming { .. }
            | smt2parser::concrete::Command::DeclareDatatype { .. }
            | smt2parser::concrete::Command::DeclareDatatypes { .. }
            | smt2parser::concrete::Command::DeclareSort { .. }
            | smt2parser::concrete::Command::DefineFun { .. }
            | smt2parser::concrete::Command::DefineFunRec { .. }
            | smt2parser::concrete::Command::DefineFunsRec { .. }
            | smt2parser::concrete::Command::DefineSort { .. }
            | smt2parser::concrete::Command::Echo { .. }
            | smt2parser::concrete::Command::Exit
            | smt2parser::concrete::Command::GetAssertions
            | smt2parser::concrete::Command::GetAssignment
            | smt2parser::concrete::Command::GetInfo { .. }
            | smt2parser::concrete::Command::GetOption { .. }
            | smt2parser::concrete::Command::GetProof
            | smt2parser::concrete::Command::GetUnsatAssumptions
            | smt2parser::concrete::Command::GetUnsatCore
            | smt2parser::concrete::Command::GetValue { .. }
            | smt2parser::concrete::Command::Pop { .. }
            | smt2parser::concrete::Command::Push { .. }
            | smt2parser::concrete::Command::Reset
            | smt2parser::concrete::Command::ResetAssertions
            | smt2parser::concrete::Command::SetInfo { .. }
            | smt2parser::concrete::Command::SetOption { .. } => {
                return Err(ParseError::Unsupported(command.to_string()))
            }
        }
    }

    let fm = match asserts.len() {
        0 => Formula::ttrue(),
        1 => asserts.pop().unwrap(),
        _ => Formula::and(asserts),
    };
    Ok(Instance::new(fm, var_manager))
}

struct FormulaBuilder<'a> {
    var_manager: &'a VarManager,
    context: Ctx,
}

impl<'a> FormulaBuilder<'a> {
    fn get_sorts(&mut self, ts: &[Term]) -> Result<Vec<Sort>, ParseError> {
        let mut sorts = Vec::with_capacity(ts.len());

        for t in ts {
            let sort = match t.sort(&mut self.context) {
                Ok(s) => match isort2sort(&s) {
                    Ok(s) => s,
                    Err(s) => return Err(s),
                },
                Err(s) => return Err(ParseError::Unsupported(format!("{}", s.0))),
            };
            sorts.push(sort);
        }
        Ok(sorts)
    }

    fn build_string_patter(&self, t: &Term) -> Result<Pattern, ParseError> {
        let mut builder = PatternBuilder {
            var_manager: self.var_manager,
        };
        let res = {
            match t.visit_with(&mut builder) {
                ControlFlow::Continue(_) => unreachable!(),
                ControlFlow::Break(Ok(p)) => p,
                ControlFlow::Break(Err(e)) => return Err(e),
            }
        };
        Ok(res)
    }

    fn build_arith_term(&self, t: &Term) -> Result<IntArithTerm, ParseError> {
        let mut builder = IntArithTermBuilder {
            var_manager: self.var_manager,
        };
        let res = {
            match t.visit_with(&mut builder) {
                ControlFlow::Continue(_) => unreachable!(),
                ControlFlow::Break(Ok(p)) => p,
                ControlFlow::Break(Err(e)) => return Err(e),
            }
        };
        Ok(res)
    }

    fn build_lin_arith_term(&self, t: &Term) -> Result<LinearArithTerm, ParseError> {
        let arith_term = self.build_arith_term(t)?;
        match LinearArithTerm::from_int_arith_term(&arith_term) {
            Some(t) => Ok(t),
            None => Err(ParseError::Unsupported(format!(
                "Nonelinear arithemtic: {}",
                arith_term
            ))),
        }
    }
}

impl<'a> Visitor<ALL> for FormulaBuilder<'a> {
    type BreakTy = Result<Formula, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(_) => todo!(),
            Term::Variable(_) => todo!(),
            Term::CoreOp(op) => match op.as_ref() {
                aws_smt_ir::CoreOp::True => ControlFlow::Break(Ok(Formula::ttrue())),
                aws_smt_ir::CoreOp::False => ControlFlow::Break(Ok(Formula::ffalse())),
                aws_smt_ir::CoreOp::Not(f) => f.visit_with(self).map_break(|t| match t {
                    Ok(t) => Ok(Formula::Not(Box::new(t))),
                    Err(e) => Err(e),
                }),
                aws_smt_ir::CoreOp::And(fs) => {
                    let mut fms = Vec::with_capacity(fs.len());
                    for f in fs {
                        match f.visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(subf)) => fms.push(subf),
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        }
                    }
                    ControlFlow::Break(Ok(Formula::And(fms)))
                }
                aws_smt_ir::CoreOp::Or(fs) => {
                    let mut fms = Vec::with_capacity(fs.len());
                    for f in fs {
                        match f.visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(subf)) => fms.push(subf),
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        }
                    }
                    ControlFlow::Break(Ok(Formula::Or(fms)))
                }
                aws_smt_ir::CoreOp::Xor(_) => todo!(),
                aws_smt_ir::CoreOp::Imp(_) => todo!(),
                aws_smt_ir::CoreOp::Eq(ts) => {
                    if ts.len() != 2 {
                        return ControlFlow::Break(Err(ParseError::SyntaxError(
                            "= needs exactly arguments".to_string(),
                            None,
                        )));
                    }
                    let sorts = match self.get_sorts(ts) {
                        Ok(s) => s,
                        Err(e) => return ControlFlow::Break(Err(e)),
                    };
                    let lhs = &ts[0];
                    let rhs = &ts[1];
                    let sort_lhs = sorts[0];
                    let sort_rhs = sorts[1];
                    match (sort_lhs, sort_rhs) {
                        (Sort::String, Sort::String) => {
                            let pat_lhs = match self.build_string_patter(lhs) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let pat_rhs = match self.build_string_patter(rhs) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let equation = WordEquation::new(pat_lhs, pat_rhs);
                            let eq_atom =
                                Formula::Atom(Atom::Predicate(Predicate::WordEquation(equation)));
                            ControlFlow::Break(Ok(eq_atom))
                        }
                        (Sort::Int, Sort::Int) => {
                            let term_lhs = match self.build_lin_arith_term(lhs) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let term_rhs = match self.build_lin_arith_term(rhs) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };

                            let equation = LinearConstraint::from_linear_arith_term(
                                &term_lhs,
                                &term_rhs,
                                LinearConstraintType::Eq,
                            );
                            ControlFlow::Break(Ok(Formula::Atom(Atom::Predicate(
                                Predicate::LinearConstraint(equation),
                            ))))
                        }
                        (Sort::Bool, Sort::Bool) => todo!("Parse boolean equivalence"),
                        (_, _) => ControlFlow::Break(Err(ParseError::SyntaxError(
                            format!("Sorts for '=' mismatch: {} and {}", sort_lhs, sort_rhs),
                            None,
                        ))),
                    }
                }
                aws_smt_ir::CoreOp::Distinct(_) => todo!(),
                aws_smt_ir::CoreOp::Ite(_, _, _) => todo!(),
            },
            Term::OtherOp(op) => match op.as_ref() {
                all::Op::Arith(arith_op) => match arith_op {
                    ArithOp::Plus(_) => todo!(),
                    ArithOp::Neg(_) => todo!(),
                    ArithOp::Minus(_) => todo!(),
                    ArithOp::Mul(_) => todo!(),
                    ArithOp::IntDiv(_) => todo!(),
                    ArithOp::RealDiv(_) => todo!(),
                    ArithOp::Divisible(_, _) => todo!(),
                    ArithOp::Mod(_, _) => todo!(),
                    ArithOp::Abs(_) => todo!(),
                    ArithOp::Lte(ts) | ArithOp::Lt(ts) | ArithOp::Gt(ts) | ArithOp::Gte(ts) => {
                        if ts.len() != 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "= needs exactly arguments".to_string(),
                                None,
                            )));
                        }
                        let sorts = match self.get_sorts(ts) {
                            Ok(s) => s,
                            Err(e) => return ControlFlow::Break(Err(e)),
                        };
                        let lhs = &ts[0];
                        let rhs = &ts[1];
                        let sort_lhs = sorts[0];
                        let sort_rhs = sorts[1];
                        match (sort_lhs, sort_rhs) {
                            (Sort::String, Sort::String) => ControlFlow::Break(Err(
                                ParseError::Unsupported("Lexicographic order".to_string()),
                            )),
                            (Sort::Int, Sort::Int) => {
                                let term_lhs = match self.build_lin_arith_term(lhs) {
                                    Ok(p) => p,
                                    Err(e) => return ControlFlow::Break(Err(e)),
                                };
                                let term_rhs = match self.build_lin_arith_term(rhs) {
                                    Ok(p) => p,
                                    Err(e) => return ControlFlow::Break(Err(e)),
                                };

                                let typ = match arith_op {
                                    ArithOp::Lte(_) => LinearConstraintType::Leq,
                                    ArithOp::Lt(_) => LinearConstraintType::Less,

                                    ArithOp::Gt(_) => LinearConstraintType::Greater,

                                    ArithOp::Gte(_) => LinearConstraintType::Geq,

                                    _ => unreachable!(),
                                };
                                let constr = LinearConstraint::from_linear_arith_term(
                                    &term_lhs, &term_rhs, typ,
                                );
                                ControlFlow::Break(Ok(Formula::Atom(Atom::Predicate(
                                    Predicate::LinearConstraint(constr),
                                ))))
                            }
                            (_, _) => ControlFlow::Break(Err(ParseError::SyntaxError(
                                format!(
                                    "Invalid arguments for '>=': {} and {}",
                                    sort_lhs, sort_rhs
                                ),
                                None,
                            ))),
                        }
                    }

                    ArithOp::ToReal(_) => todo!(),
                    ArithOp::ToInt(_) => todo!(),
                    ArithOp::IsInt(_) => todo!(),
                },
                all::Op::Array(_) => todo!(),
                all::Op::BitVec(_) => todo!(),
                all::Op::Set(_) => todo!(),
                all::Op::String(_) => todo!(),
            },
            Term::UF(_) => todo!(),
            Term::Let(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Quantifier(_) => todo!(),
        }
    }

    fn visit_const(
        &mut self,
        _constant: &aws_smt_ir::IConst,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        aws_smt_ir::visit::ControlFlow::CONTINUE
    }

    fn visit_var(
        &mut self,
        _var: &aws_smt_ir::IVar<<ALL as aws_smt_ir::Logic>::Var>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        aws_smt_ir::visit::ControlFlow::CONTINUE
    }

    fn visit_core_op(
        &mut self,
        op: &aws_smt_ir::ICoreOp<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }

    fn visit_theory_op(
        &mut self,
        op: &aws_smt_ir::IOp<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }

    fn visit_uninterpreted_func(
        &mut self,
        uf: &aws_smt_ir::IUF<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        uf.super_visit_with(self)
    }

    fn visit_let(
        &mut self,
        l: &aws_smt_ir::ILet<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        l.super_visit_with(self)
    }

    fn visit_match(
        &mut self,
        m: &aws_smt_ir::IMatch<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        m.super_visit_with(self)
    }

    fn visit_quantifier(
        &mut self,
        quantifier: &aws_smt_ir::IQuantifier<ALL>,
    ) -> aws_smt_ir::visit::ControlFlow<Self::BreakTy> {
        quantifier.super_visit_with(self)
    }

    fn context(&self) -> Option<&Ctx> {
        Some(&self.context)
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        debug_assert!(
            self.context().is_none(),
            "context() and context_mut() should be implemented together"
        );
        Some(&mut self.context)
    }
}

struct PatternBuilder<'a> {
    var_manager: &'a VarManager,
}

impl<'a> Visitor<ALL> for PatternBuilder<'a> {
    type BreakTy = Result<Pattern, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                all::Op::String(sop) => match sop {
                    StringOp::StrConcat(ts) => {
                        let mut pat = Pattern::empty();
                        for t in ts {
                            match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => pat.extend(p),
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            }
                        }
                        ControlFlow::Break(Ok(pat))
                    }
                    StringOp::Len(_)
                    | StringOp::LexOrd(_)
                    | StringOp::ToRe(_)
                    | StringOp::InRe(_, _)
                    | StringOp::ReNone
                    | StringOp::ReAll
                    | StringOp::ReAllChar
                    | StringOp::ReConcat(_)
                    | StringOp::ReUnion(_)
                    | StringOp::ReIntersect(_)
                    | StringOp::ReKleeneStar(_)
                    | StringOp::RefClosLexOrd(_)
                    | StringOp::SingStrAt(_, _)
                    | StringOp::Substr(_, _, _)
                    | StringOp::PrefixOf(_, _)
                    | StringOp::SuffixOf(_, _)
                    | StringOp::Contains(_, _)
                    | StringOp::IndexOf(_, _, _)
                    | StringOp::Replace(_, _, _)
                    | StringOp::ReplaceAll(_, _, _)
                    | StringOp::ReplaceRe(_, _, _)
                    | StringOp::ReplaceReAll(_, _, _)
                    | StringOp::ReCompl(_)
                    | StringOp::ReDiff(_)
                    | StringOp::ReKleeneCross(_)
                    | StringOp::ReOpt(_)
                    | StringOp::ReRange(_, _)
                    | StringOp::RePow(_, _)
                    | StringOp::ReLoop(_, _)
                    | StringOp::IsDigit(_)
                    | StringOp::ToCode(_)
                    | StringOp::FromCode(_)
                    | StringOp::ToInt(_)
                    | StringOp::FromInt(_) => ControlFlow::Break(Err(ParseError::Unsupported(
                        "String operation".to_string(),
                    ))),
                },
                all::Op::Arith(_) | all::Op::Array(_) | all::Op::BitVec(_) | all::Op::Set(_) => {
                    ControlFlow::Break(Err(ParseError::Unsupported(
                        "Non-String operation".to_string(),
                    )))
                }
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(
                    "Non-String operation".to_string(),
                )))
            }
        }
    }

    fn visit_const(&mut self, constant: &aws_smt_ir::IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            aws_smt_ir::Constant::String(s) => ControlFlow::Break(Ok(Pattern::constant(s))),
            aws_smt_ir::Constant::Numeral(_)
            | aws_smt_ir::Constant::Decimal(_)
            | aws_smt_ir::Constant::Hexadecimal(_)
            | aws_smt_ir::Constant::Binary(_) => ControlFlow::Break(Err(ParseError::SyntaxError(
                "Can only concatenate string constants".to_string(),
                None,
            ))),
        }
    }

    fn visit_var(
        &mut self,
        var: &aws_smt_ir::IVar<<ALL as aws_smt_ir::Logic>::Var>,
    ) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.var_manager.by_name(name) {
            if vvar.sort() != Sort::String {
                return ControlFlow::Break(Err(ParseError::SyntaxError(
                    format!("Expected string variable but found {} ", vvar.sort()),
                    None,
                )));
            }
            ControlFlow::Break(Ok(Pattern::variable(vvar)))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

struct IntArithTermBuilder<'a> {
    var_manager: &'a VarManager,
}

impl<'a> Visitor<ALL> for IntArithTermBuilder<'a> {
    type BreakTy = Result<IntArithTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                all::Op::Arith(arith_op) => match arith_op {
                    ArithOp::Plus(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
                                None,
                            )));
                        }
                        let mut iter = ts.iter();
                        let mut lhs = match iter.next().unwrap().visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(p)) => p,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        for t in iter {
                            let rhs = match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => p,
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            };
                            lhs = IntArithTerm::plus(&lhs, &rhs);
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    ArithOp::Neg(t) => match t.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(p)) => ControlFlow::Break(Ok(IntArithTerm::neg(&p))),
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    ArithOp::Minus(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
                                None,
                            )));
                        }
                        let mut iter = ts.iter();
                        let mut lhs = match iter.next().unwrap().visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(p)) => p,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        for t in iter {
                            let rhs = match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => p,
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            };
                            lhs = IntArithTerm::plus(&lhs, &rhs.neg());
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    ArithOp::Mul(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
                                None,
                            )));
                        }
                        let mut iter = ts.iter();
                        let mut lhs = match iter.next().unwrap().visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(p)) => p,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        for t in iter {
                            let rhs = match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => p,
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            };
                            lhs = IntArithTerm::times(&lhs, &rhs);
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    ArithOp::IntDiv(_)
                    | ArithOp::RealDiv(_)
                    | ArithOp::Divisible(_, _)
                    | ArithOp::Mod(_, _)
                    | ArithOp::Abs(_)
                    | ArithOp::Gte(_)
                    | ArithOp::Gt(_)
                    | ArithOp::Lte(_)
                    | ArithOp::Lt(_)
                    | ArithOp::ToReal(_)
                    | ArithOp::ToInt(_)
                    | ArithOp::IsInt(_) => {
                        ControlFlow::Break(Err(ParseError::Unsupported(arith_op.to_string())))
                    }
                },
                all::Op::String(StringOp::Len(ts)) => {
                    let mut builder = StringLenToArithBuilder {
                        var_manager: self.var_manager,
                    };
                    match ts.visit_with(&mut builder) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(p)) => ControlFlow::Break(Ok(p)),
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    }
                }
                all::Op::String(_) | all::Op::Array(_) | all::Op::BitVec(_) | all::Op::Set(_) => {
                    ControlFlow::Break(Err(ParseError::Unsupported(
                        "Non-String operation".to_string(),
                    )))
                }
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(
                    "Non-String operation".to_string(),
                )))
            }
        }
    }

    fn visit_const(&mut self, constant: &aws_smt_ir::IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            aws_smt_ir::Constant::Numeral(n) => {
                let as_isize: Result<isize, _> = n.try_into();
                match as_isize {
                    Ok(i) => ControlFlow::Break(Ok(IntArithTerm::constant(i))),
                    Err(_) => ControlFlow::Break(Err(ParseError::SyntaxError(
                        format!("Integer constant out of range: {}", n),
                        None,
                    ))),
                }
            }
            aws_smt_ir::Constant::String(_)
            | aws_smt_ir::Constant::Decimal(_)
            | aws_smt_ir::Constant::Hexadecimal(_)
            | aws_smt_ir::Constant::Binary(_) => ControlFlow::Break(Err(ParseError::SyntaxError(
                format!("Expected numeral constant but found {}", constant),
                None,
            ))),
        }
    }

    fn visit_var(
        &mut self,
        var: &aws_smt_ir::IVar<<ALL as aws_smt_ir::Logic>::Var>,
    ) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.var_manager.by_name(name) {
            if vvar.sort() != Sort::Int {
                return ControlFlow::Break(Err(ParseError::SyntaxError(
                    format!("Expected int variable but found {} ", vvar.sort()),
                    None,
                )));
            }
            ControlFlow::Break(Ok(IntArithTerm::var(vvar)))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

pub struct StringLenToArithBuilder<'a> {
    var_manager: &'a VarManager,
}

impl<'a> Visitor<ALL> for StringLenToArithBuilder<'a> {
    type BreakTy = Result<IntArithTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                all::Op::String(sop) => match sop {
                    StringOp::StrConcat(ts) => {
                        // Sum all lengths
                        let mut iter = ts.iter();
                        let mut lhs = match iter.next().unwrap().visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(p)) => p,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        for t in iter {
                            match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => lhs = IntArithTerm::plus(&lhs, &p),
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            }
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    StringOp::Len(_)
                    | StringOp::LexOrd(_)
                    | StringOp::ToRe(_)
                    | StringOp::InRe(_, _)
                    | StringOp::ReNone
                    | StringOp::ReAll
                    | StringOp::ReAllChar
                    | StringOp::ReConcat(_)
                    | StringOp::ReUnion(_)
                    | StringOp::ReIntersect(_)
                    | StringOp::ReKleeneStar(_)
                    | StringOp::RefClosLexOrd(_)
                    | StringOp::SingStrAt(_, _)
                    | StringOp::Substr(_, _, _)
                    | StringOp::PrefixOf(_, _)
                    | StringOp::SuffixOf(_, _)
                    | StringOp::Contains(_, _)
                    | StringOp::IndexOf(_, _, _)
                    | StringOp::Replace(_, _, _)
                    | StringOp::ReplaceAll(_, _, _)
                    | StringOp::ReplaceRe(_, _, _)
                    | StringOp::ReplaceReAll(_, _, _)
                    | StringOp::ReCompl(_)
                    | StringOp::ReDiff(_)
                    | StringOp::ReKleeneCross(_)
                    | StringOp::ReOpt(_)
                    | StringOp::ReRange(_, _)
                    | StringOp::RePow(_, _)
                    | StringOp::ReLoop(_, _)
                    | StringOp::IsDigit(_)
                    | StringOp::ToCode(_)
                    | StringOp::FromCode(_)
                    | StringOp::ToInt(_)
                    | StringOp::FromInt(_) => ControlFlow::Break(Err(ParseError::Unsupported(
                        format!("Expected string term but found {}", sop),
                    ))),
                },
                all::Op::Arith(_) | all::Op::Array(_) | all::Op::BitVec(_) | all::Op::Set(_) => {
                    ControlFlow::Break(Err(ParseError::Unsupported(format!(
                        "Expected string term but found {}",
                        s
                    ))))
                }
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(format!(
                    "Expected string term but found {}",
                    term
                ))))
            }
        }
    }

    fn visit_const(&mut self, constant: &aws_smt_ir::IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            aws_smt_ir::Constant::String(s) => {
                ControlFlow::Break(Ok(IntArithTerm::Const(s.chars().count() as isize)))
            }
            aws_smt_ir::Constant::Numeral(_)
            | aws_smt_ir::Constant::Decimal(_)
            | aws_smt_ir::Constant::Hexadecimal(_)
            | aws_smt_ir::Constant::Binary(_) => ControlFlow::Break(Err(ParseError::Unsupported(
                format!("Expected string term but found {}", constant),
            ))),
        }
    }

    fn visit_var(
        &mut self,
        var: &aws_smt_ir::IVar<<ALL as aws_smt_ir::Logic>::Var>,
    ) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.var_manager.by_name(name) {
            if vvar.sort() != Sort::String {
                return ControlFlow::Break(Err(ParseError::SyntaxError(
                    format!("Expected string variable but found {} ", vvar.sort()),
                    None,
                )));
            }
            ControlFlow::Break(Ok(IntArithTerm::Var(
                self.var_manager.str_length_var(vvar).unwrap().clone(),
            )))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

fn isort2sort(sort: &ISort) -> Result<Sort, ParseError> {
    match sort.as_ref() {
        aws_smt_ir::Sort::Simple { identifier } => match identifier.as_ref() {
            aws_smt_ir::Identifier::Simple { symbol } => match symbol.0.to_lowercase().as_str() {
                "string" => Ok(Sort::String),
                "int" => Ok(Sort::Int),
                "bool" => Ok(Sort::Bool),
                _ => Err(ParseError::Unsupported(format!("Sort {}", symbol.0))),
            },
            aws_smt_ir::Identifier::Indexed { symbol, .. } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
        },
        aws_smt_ir::Sort::Parameterized { identifier, .. } => match identifier.as_ref() {
            aws_smt_ir::Identifier::Simple { symbol } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
            aws_smt_ir::Identifier::Indexed { symbol, .. } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
        },
    }
}
