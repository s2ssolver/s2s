use std::{fmt::format, io::BufRead};

use aws_smt_ir::{
    logic::ALL,
    visit::{ControlFlow, SuperVisit, Visit, Visitor},
    Ctx, ISort, Script, Sorted, Term,
};

use crate::{
    formula::{Atom, Formula, Predicate},
    model::{
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
                let v = var_manager.new_var(&symbol.0, isort2sort(&sort)?);
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
        0 => Formula::True,
        1 => asserts.pop().unwrap(),
        _ => Formula::And(asserts),
    };
    Ok(Instance::new(fm, var_manager))
}

struct FormulaBuilder<'a> {
    var_manager: &'a VarManager,
    context: Ctx,
}

impl<'a> Visitor<ALL> for FormulaBuilder<'a> {
    type BreakTy = Result<Formula, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(_) => todo!(),
            Term::Variable(_) => todo!(),
            Term::CoreOp(op) => match op.as_ref() {
                aws_smt_ir::CoreOp::True => ControlFlow::Break(Ok(Formula::True)),
                aws_smt_ir::CoreOp::False => ControlFlow::Break(Ok(Formula::False)),
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
                    ControlFlow::Break(Ok(Formula::And(fms)))
                }
                aws_smt_ir::CoreOp::Xor(_) => todo!(),
                aws_smt_ir::CoreOp::Imp(_) => todo!(),
                aws_smt_ir::CoreOp::Eq(ts) => {
                    if ts.len() == 2 {
                        let lhs = &ts[0];
                        let rhs = &ts[1];

                        let sort_lhs = match lhs.sort(&mut self.context_mut().unwrap()) {
                            Ok(s) => match isort2sort(&s) {
                                Ok(s) => s,
                                Err(s) => return ControlFlow::Break(Err(s)),
                            },
                            Err(s) => {
                                return ControlFlow::Break(Err(ParseError::Unsupported(
                                    s.to_string(),
                                )))
                            }
                        };
                        let sort_rhs = match rhs.sort(&mut self.context_mut().unwrap()) {
                            Ok(s) => match isort2sort(&s) {
                                Ok(s) => s,
                                Err(s) => return ControlFlow::Break(Err(s)),
                            },
                            Err(s) => {
                                return ControlFlow::Break(Err(ParseError::Unsupported(
                                    s.to_string(),
                                )))
                            }
                        };

                        match (sort_lhs, sort_rhs) {
                            (Sort::String, Sort::String) => {
                                let mut builder = PatternBuilder {
                                    var_manager: self.var_manager,
                                    context: Ctx::default(),
                                };
                                let pat_lhs = {
                                    match lhs.visit_with(&mut builder) {
                                        ControlFlow::Continue(_) => unreachable!(),
                                        ControlFlow::Break(Ok(p)) => p,
                                        ControlFlow::Break(Err(e)) => {
                                            return ControlFlow::Break(Err(e))
                                        }
                                    }
                                };

                                let pat_rhs = {
                                    match rhs.visit_with(&mut builder) {
                                        ControlFlow::Continue(_) => unreachable!(),
                                        ControlFlow::Break(Ok(p)) => p,
                                        ControlFlow::Break(Err(e)) => {
                                            return ControlFlow::Break(Err(e))
                                        }
                                    }
                                };
                                let equation = WordEquation::new(pat_lhs, pat_rhs);
                                ControlFlow::Break(Ok(Formula::Atom(Atom::Predicate(
                                    Predicate::WordEquation(equation),
                                ))))
                            }
                            (Sort::Int, Sort::Int) => todo!("Parse linear constraint"),
                            (Sort::Bool, Sort::Bool) => todo!("Parse boolean equivalence"),
                            (_, _) => {
                                return ControlFlow::Break(Err(ParseError::SyntaxError(
                                    format!(
                                        "Sorts for '=' mismatch: {} and {}",
                                        sort_lhs, sort_rhs
                                    ),
                                    None,
                                )))
                            }
                        }
                    } else {
                        return ControlFlow::Break(Err(ParseError::SyntaxError(
                            "= needs exactly arguments".to_string(),
                            None,
                        )));
                    }
                }
                aws_smt_ir::CoreOp::Distinct(_) => todo!(),
                aws_smt_ir::CoreOp::Ite(_, _, _) => todo!(),
            },
            Term::OtherOp(_) => todo!(),
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
    context: Ctx,
}

impl<'a> Visitor<ALL> for PatternBuilder<'a> {
    type BreakTy = Result<Pattern, ParseError>;

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

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                aws_smt_ir::logic::all::Op::String(sop) => match sop {
                    aws_smt_ir::logic::StringOp::StrConcat(ts) => {
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
                    aws_smt_ir::logic::StringOp::Len(_)
                    | aws_smt_ir::logic::StringOp::LexOrd(_)
                    | aws_smt_ir::logic::StringOp::ToRe(_)
                    | aws_smt_ir::logic::StringOp::InRe(_, _)
                    | aws_smt_ir::logic::StringOp::ReNone
                    | aws_smt_ir::logic::StringOp::ReAll
                    | aws_smt_ir::logic::StringOp::ReAllChar
                    | aws_smt_ir::logic::StringOp::ReConcat(_)
                    | aws_smt_ir::logic::StringOp::ReUnion(_)
                    | aws_smt_ir::logic::StringOp::ReIntersect(_)
                    | aws_smt_ir::logic::StringOp::ReKleeneStar(_)
                    | aws_smt_ir::logic::StringOp::RefClosLexOrd(_)
                    | aws_smt_ir::logic::StringOp::SingStrAt(_, _)
                    | aws_smt_ir::logic::StringOp::Substr(_, _, _)
                    | aws_smt_ir::logic::StringOp::PrefixOf(_, _)
                    | aws_smt_ir::logic::StringOp::SuffixOf(_, _)
                    | aws_smt_ir::logic::StringOp::Contains(_, _)
                    | aws_smt_ir::logic::StringOp::IndexOf(_, _, _)
                    | aws_smt_ir::logic::StringOp::Replace(_, _, _)
                    | aws_smt_ir::logic::StringOp::ReplaceAll(_, _, _)
                    | aws_smt_ir::logic::StringOp::ReplaceRe(_, _, _)
                    | aws_smt_ir::logic::StringOp::ReplaceReAll(_, _, _)
                    | aws_smt_ir::logic::StringOp::ReCompl(_)
                    | aws_smt_ir::logic::StringOp::ReDiff(_)
                    | aws_smt_ir::logic::StringOp::ReKleeneCross(_)
                    | aws_smt_ir::logic::StringOp::ReOpt(_)
                    | aws_smt_ir::logic::StringOp::ReRange(_, _)
                    | aws_smt_ir::logic::StringOp::RePow(_, _)
                    | aws_smt_ir::logic::StringOp::ReLoop(_, _)
                    | aws_smt_ir::logic::StringOp::IsDigit(_)
                    | aws_smt_ir::logic::StringOp::ToCode(_)
                    | aws_smt_ir::logic::StringOp::FromCode(_)
                    | aws_smt_ir::logic::StringOp::ToInt(_)
                    | aws_smt_ir::logic::StringOp::FromInt(_) => ControlFlow::Break(Err(
                        ParseError::Unsupported("String operation".to_string()),
                    )),
                },
                aws_smt_ir::logic::all::Op::Arith(_)
                | aws_smt_ir::logic::all::Op::Array(_)
                | aws_smt_ir::logic::all::Op::BitVec(_)
                | aws_smt_ir::logic::all::Op::Set(_) => ControlFlow::Break(Err(
                    ParseError::Unsupported("Non-String operation".to_string()),
                )),
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
