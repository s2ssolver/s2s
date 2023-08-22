use std::io::BufRead;

use aws_smt_ir::{
    logic::{all::Op, ArithOp, StringOp, ALL},
    visit::{ControlFlow, Visit, Visitor},
    Constant, CoreOp, Ctx, IConst, ISort, IVar, Identifier, Logic, Script, Sort, Sorted, Term,
};
use num_bigint::BigUint;
use smallvec::smallvec;
use smt2parser::concrete::Command;

use crate::{
    model::formula::{Formula, Predicate},
    model::{
        terms::{IntTerm, ReTerm, StringTerm},
        Sort as NSort, Variable,
    },
};

use super::{util::unescape, Instance, ParseError};

pub fn parse_smt<R: BufRead>(smt: R) -> Result<Instance, ParseError> {
    let script = Script::<Term>::parse(smt)
        .map_err(|e| ParseError::Other(format!("Error parsing SMT-LIB script: {}", e)))?;
    let mut instance = Instance::default();

    let mut asserts = vec![];
    for command in script {
        match command {
            Command::Assert { term } => {
                let mut visitor = FormulaBuilder {
                    instance: &instance,
                    context: Ctx::default(),
                };
                match term.visit_with(&mut visitor) {
                    ControlFlow::Continue(_) => unreachable!(),
                    ControlFlow::Break(res) => asserts.push(res?),
                }
            }
            Command::DeclareConst { symbol, sort } => {
                instance.add_var(Variable::new(symbol.0.clone(), isort2sort(&sort)?));
            }
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                if parameters.is_empty() {
                    // This is a constant function, i.e., a variable
                    instance.add_var(Variable::new(symbol.0.clone(), isort2sort(&sort)?));
                } else {
                    return Err(ParseError::Unsupported(
                        "Non-constant function declaration".to_string(),
                    ));
                }
            }
            Command::CheckSat
            | Command::SetLogic { .. }
            | Command::GetModel
            | Command::GetOption { .. }
            | Command::SetOption { .. }
            | Command::SetInfo { .. }
            | Command::Exit => {
                // Ignore
                log::debug!("Ignoring command: {:?}", command)
            }
            Command::CheckSatAssuming { .. }
            | Command::DeclareDatatype { .. }
            | Command::DeclareDatatypes { .. }
            | Command::DeclareSort { .. }
            | Command::DefineFun { .. }
            | Command::DefineFunRec { .. }
            | Command::DefineFunsRec { .. }
            | Command::DefineSort { .. }
            | Command::Echo { .. }
            | Command::GetAssertions
            | Command::GetAssignment
            | Command::GetInfo { .. }
            | Command::GetProof
            | Command::GetUnsatAssumptions
            | Command::GetUnsatCore
            | Command::GetValue { .. }
            | Command::Pop { .. }
            | Command::Push { .. }
            | Command::Reset
            | Command::ResetAssertions => return Err(ParseError::Unsupported(command.to_string())),
        }
    }

    let fm = match asserts.len() {
        0 => Formula::ttrue(),
        1 => asserts.pop().unwrap(),
        _ => Formula::and(asserts),
    };
    instance.set_formula(fm);
    Ok(instance)
}

struct FormulaBuilder<'a> {
    instance: &'a Instance,
    context: Ctx,
}

impl<'a> FormulaBuilder<'a> {
    fn get_sorts(&mut self, ts: &[Term]) -> Result<Vec<NSort>, ParseError> {
        let mut sorts = Vec::with_capacity(ts.len());

        for t in ts {
            if let Term::Variable(v) = t {
                match v.as_ref() {
                    aws_smt_ir::QualIdentifier::Simple { identifier }
                    | aws_smt_ir::QualIdentifier::Sorted { identifier, .. } => {
                        match self.instance.var_by_name(&identifier.to_string()) {
                            Some(vv) => sorts.push(vv.sort()),
                            None => todo!(),
                        }
                    }
                }
            } else {
                let sort = match t.sort(&mut self.context) {
                    Ok(s) => match isort2sort(&s) {
                        Ok(s) => s,
                        Err(s) => return Err(s),
                    },
                    Err(s) => return Err(ParseError::Other(format!("{}", s))),
                };
                sorts.push(sort);
            }
        }
        Ok(sorts)
    }
}

impl<'a> Visitor<ALL> for FormulaBuilder<'a> {
    type BreakTy = Result<Formula, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(_) => todo!(),
            Term::Variable(v) => v.visit_with(self),
            Term::CoreOp(op) => match op.as_ref() {
                CoreOp::True => ControlFlow::Break(Ok(Formula::ttrue())),
                CoreOp::False => ControlFlow::Break(Ok(Formula::ffalse())),
                CoreOp::Not(f) => f.visit_with(self).map_break(|t| match t {
                    Ok(t) => Ok(Formula::Not(Box::new(t))),
                    Err(e) => Err(e),
                }),
                CoreOp::And(fs) => {
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
                CoreOp::Or(fs) => {
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
                CoreOp::Xor(_) => todo!(),
                CoreOp::Imp(ts) => {
                    if ts.len() != 2 {
                        return ControlFlow::Break(Err(ParseError::SyntaxError(
                            "= needs exactly arguments".to_string(),
                        )));
                    }
                    let sorts = match self.get_sorts(ts) {
                        Ok(s) => s,
                        Err(e) => return ControlFlow::Break(Err(e)),
                    };
                    if sorts[0] != NSort::Bool || sorts[1] != NSort::Bool {
                        return ControlFlow::Break(Err(ParseError::SyntaxError(
                            "Invalid arguments for '=>': expected bool and bool".to_string(),
                        )));
                    }
                    // Rewrite as -lhs \/ rhs
                    let lhs = &ts[0];
                    let rhs = &ts[1];
                    let lhs = match lhs.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => t,
                        ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                    };
                    let rhs = match rhs.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => t,
                        ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                    };
                    let imp_ltr = Formula::or(vec![Formula::not(lhs), rhs]);
                    ControlFlow::Break(Ok(imp_ltr))
                }
                CoreOp::Eq(ts) => {
                    if ts.len() != 2 {
                        return ControlFlow::Break(Err(ParseError::SyntaxError(
                            "= needs exactly arguments".to_string(),
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
                        (NSort::String, NSort::String) => {
                            let pat_lhs = match build_string_term(lhs, self.instance) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let pat_rhs = match build_string_term(rhs, self.instance) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let equation = Predicate::Equality(pat_lhs.into(), pat_rhs.into());
                            let eq_atom = Formula::predicate(equation);
                            ControlFlow::Break(Ok(eq_atom))
                        }
                        (NSort::Int, NSort::Int) => {
                            let term_lhs = match build_int_term(lhs, self.instance) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };
                            let term_rhs = match build_int_term(rhs, self.instance) {
                                Ok(p) => p,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            };

                            let equation = Predicate::Equality(term_lhs.into(), term_rhs.into());
                            ControlFlow::Break(Ok(Formula::predicate(equation)))
                        }
                        (NSort::Bool, NSort::Bool) => {
                            // Rewrite as dual implication
                            // (-lhs \/ rhs) /\ (lhs \/ -rhs)
                            let lhs = match lhs.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(t)) => t,
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            };
                            let rhs = match rhs.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(t)) => t,
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            };
                            let imp_ltr = Formula::or(vec![Formula::not(lhs.clone()), rhs.clone()]);
                            let imp_rtl = Formula::or(vec![Formula::not(rhs), lhs]);
                            ControlFlow::Break(Ok(Formula::and(vec![imp_ltr, imp_rtl])))
                        }
                        (_, _) => ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                            "Sorts for '=' mismatch: {} and {}",
                            sort_lhs, sort_rhs
                        )))),
                    }
                }
                CoreOp::Distinct(_) => todo!(),
                CoreOp::Ite(p, t, f) => {
                    // Rewrite as (p -> t) /\ (-p -> f)
                    let imp1 = Term::CoreOp(CoreOp::Imp(smallvec![p.clone(), t.clone()]).into());
                    let imp2 = Term::CoreOp(
                        CoreOp::Imp(smallvec![
                            Term::CoreOp(CoreOp::Not(p.clone()).into()),
                            f.clone()
                        ])
                        .into(),
                    );
                    let conj = Term::CoreOp(CoreOp::And(smallvec![imp1, imp2]).into());

                    conj.visit_with(self)
                }
            },
            Term::OtherOp(op) => match op.as_ref() {
                Op::Arith(arith_op) => match arith_op {
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
                            (NSort::String, NSort::String) => ControlFlow::Break(Err(
                                ParseError::Unsupported("Lexicographic order".to_string()),
                            )),
                            (NSort::Int, NSort::Int) => {
                                let term_lhs = match build_int_term(lhs, self.instance) {
                                    Ok(p) => p,
                                    Err(e) => return ControlFlow::Break(Err(e)),
                                };
                                let term_rhs = match build_int_term(rhs, self.instance) {
                                    Ok(p) => p,
                                    Err(e) => return ControlFlow::Break(Err(e)),
                                };

                                let pred = match arith_op {
                                    ArithOp::Lte(_) => {
                                        Predicate::Leq(term_lhs.into(), term_rhs.into())
                                    }
                                    ArithOp::Lt(_) => {
                                        Predicate::Less(term_lhs.into(), term_rhs.into())
                                    }
                                    ArithOp::Gt(_) => {
                                        Predicate::Greater(term_lhs.into(), term_rhs.into())
                                    }
                                    ArithOp::Gte(_) => {
                                        Predicate::Geq(term_lhs.into(), term_rhs.into())
                                    }
                                    _ => unreachable!(),
                                };

                                ControlFlow::Break(Ok(Formula::predicate(pred)))
                            }
                            (_, _) => ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                                "Invalid arguments for '>=': {} and {}",
                                sort_lhs, sort_rhs
                            )))),
                        }
                    }

                    ArithOp::ToReal(_) => todo!(),
                    ArithOp::ToInt(_) => todo!(),
                    ArithOp::IsInt(_) => todo!(),
                },
                Op::Array(_) => todo!(),
                Op::BitVec(_) => todo!(),
                Op::Set(_) => todo!(),
                Op::String(string_op) => match string_op {
                    StringOp::InRe(t, r) => {
                        let pat = match build_string_term(t, self.instance) {
                            Ok(p) => p,
                            Err(e) => return ControlFlow::Break(Err(e)),
                        };
                        let re = match build_re_term(r, self.instance) {
                            Ok(p) => p,
                            Err(e) => return ControlFlow::Break(Err(e)),
                        };
                        let pred = Predicate::In(pat.into(), re.into());
                        ControlFlow::Break(Ok(Formula::predicate(pred)))
                    }
                    StringOp::LexOrd(_)
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
                    | StringOp::IsDigit(_)
                    | StringOp::ReplaceReAll(_, _, _) => {
                        ControlFlow::Break(Err(ParseError::Unsupported(format!("{}", string_op))))
                    }

                    _ => ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                        "Unexpected string operation: {}",
                        string_op
                    )))),
                },
            },
            Term::UF(_) => todo!(),
            Term::Let(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Quantifier(_) => todo!(),
        }
    }

    fn visit_var(&mut self, var: &IVar<<ALL as Logic>::Var>) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.instance.var_by_name(name) {
            if vvar.sort() != NSort::Bool {
                return ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                    "Expected Boolean variable but found {} ",
                    vvar.sort()
                ))));
            }
            ControlFlow::Break(Ok(Formula::boolvar(vvar.clone())))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        debug_assert!(
            self.context().is_none(),
            "context() and context_mut() should be implemented together"
        );
        Some(&mut self.context)
    }
}

fn build_string_term(t: &Term, instance: &Instance) -> Result<StringTerm, ParseError> {
    let mut builder = StringTermBuilder { instance };
    let res = {
        match t.visit_with(&mut builder) {
            ControlFlow::Continue(_) => unreachable!(),
            ControlFlow::Break(Ok(p)) => p,
            ControlFlow::Break(Err(e)) => return Err(e),
        }
    };
    Ok(res)
}

fn build_int_term(t: &Term, instance: &Instance) -> Result<IntTerm, ParseError> {
    let mut builder = IntArithTermBuilder { instance };
    let res = {
        match t.visit_with(&mut builder) {
            ControlFlow::Continue(_) => unreachable!(),
            ControlFlow::Break(Ok(p)) => p,
            ControlFlow::Break(Err(e)) => return Err(e),
        }
    };
    Ok(res)
}

fn build_re_term(t: &Term, instance: &Instance) -> Result<ReTerm, ParseError> {
    let mut builder = ReTermBuilder { instance };
    let res = {
        match t.visit_with(&mut builder) {
            ControlFlow::Continue(_) => unreachable!(),
            ControlFlow::Break(Ok(p)) => p,
            ControlFlow::Break(Err(e)) => return Err(e),
        }
    };
    Ok(res)
}

struct StringTermBuilder<'a> {
    instance: &'a Instance,
}

impl<'a> Visitor<ALL> for StringTermBuilder<'a> {
    type BreakTy = Result<StringTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                Op::String(sop) => match sop {
                    StringOp::StrConcat(ts) => {
                        let mut pat = StringTerm::empty();
                        for t in ts {
                            match t.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(p)) => pat = StringTerm::concat(pat, p),
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
                Op::Arith(_) | Op::Array(_) | Op::BitVec(_) | Op::Set(_) => {
                    ControlFlow::Break(Err(ParseError::Unsupported(format!(
                        "1Non-String operation: {}",
                        s
                    ))))
                }
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(format!(
                    "2Non-String operation: {}",
                    term
                ))))
            }
        }
    }

    fn visit_const(&mut self, constant: &IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            Constant::String(s) => match unescape(s, false) {
                Ok(s) => ControlFlow::Break(Ok(StringTerm::Constant(s))),
                Err(e) => ControlFlow::Break(Err(e)),
            },
            Constant::Numeral(_)
            | Constant::Decimal(_)
            | Constant::Hexadecimal(_)
            | Constant::Binary(_) => ControlFlow::Break(Err(ParseError::SyntaxError(
                "Can only concatenate string constants".to_string(),
            ))),
        }
    }

    fn visit_var(&mut self, var: &IVar<<ALL as Logic>::Var>) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.instance.var_by_name(name) {
            if vvar.sort() != NSort::String {
                return ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                    "Expected string variable but found {} ",
                    vvar.sort()
                ))));
            }
            ControlFlow::Break(Ok(StringTerm::variable(vvar)))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

struct ReTermBuilder<'a> {
    instance: &'a Instance,
}

impl<'a> Visitor<ALL> for ReTermBuilder<'a> {
    type BreakTy = Result<ReTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                Op::String(sop) => match sop {
                    StringOp::ToRe(t) => match build_string_term(t, self.instance) {
                        Ok(p) => ControlFlow::Break(Ok(ReTerm::String(p))),
                        Err(e) => ControlFlow::Break(Err(e)),
                    },
                    StringOp::ReNone => ControlFlow::Break(Ok(ReTerm::None)),
                    StringOp::ReAll => ControlFlow::Break(Ok(ReTerm::All)),
                    StringOp::ReAllChar => ControlFlow::Break(Ok(ReTerm::Any)),
                    StringOp::ReConcat(rs) => {
                        let mut res = Vec::with_capacity(rs.len());
                        for r in rs {
                            match r.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(t)) => res.push(t),
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            }
                        }
                        ControlFlow::Break(Ok(ReTerm::Concat(res)))
                    }
                    StringOp::ReUnion(rs) => {
                        let mut res = Vec::with_capacity(rs.len());
                        for r in rs {
                            match r.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(t)) => res.push(t),
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            }
                        }
                        ControlFlow::Break(Ok(ReTerm::Union(res)))
                    }
                    StringOp::ReIntersect(rs) => {
                        let mut res = Vec::with_capacity(rs.len());
                        for r in rs {
                            match r.visit_with(self) {
                                ControlFlow::Continue(_) => unreachable!(),
                                ControlFlow::Break(Ok(t)) => res.push(t),
                                ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                            }
                        }
                        ControlFlow::Break(Ok(ReTerm::Inter(res)))
                    }
                    StringOp::ReKleeneStar(r) => match r.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => {
                            ControlFlow::Break(Ok(ReTerm::Star(Box::new(t))))
                        }
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    StringOp::ReCompl(r) => match r.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => {
                            ControlFlow::Break(Ok(ReTerm::Comp(Box::new(t))))
                        }
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    StringOp::ReDiff(rs) => {
                        if rs.len() != 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "Regular Difference needs exactly two arguments".to_string(),
                            )));
                        }
                        let lhs = match rs[0].visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(t)) => t,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        let rhs = match rs[1].visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(t)) => t,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        ControlFlow::Break(Ok(ReTerm::Diff(Box::new(lhs), Box::new(rhs))))
                    }
                    StringOp::ReKleeneCross(r) => match r.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => {
                            ControlFlow::Break(Ok(ReTerm::Plus(Box::new(t))))
                        }
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    StringOp::ReOpt(r) => match r.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(t)) => {
                            ControlFlow::Break(Ok(ReTerm::Optional(Box::new(t))))
                        }
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    StringOp::ReRange(l, u) => {
                        let lterm = match build_string_term(l, self.instance) {
                            Ok(p) => p,
                            Err(e) => return ControlFlow::Break(Err(e)),
                        };
                        let uterm = match build_string_term(u, self.instance) {
                            Ok(p) => p,
                            Err(e) => return ControlFlow::Break(Err(e)),
                        };
                        ControlFlow::Break(Ok(ReTerm::Range(lterm, uterm)))
                    }
                    StringOp::RePow(i, r) => {
                        let exp = match i[0].as_ref() {
                            smt2parser::visitors::Index::Numeral(n) => match biguint2isize(n) {
                                Ok(i) => i,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            },
                            smt2parser::visitors::Index::Symbol(_) => {
                                return ControlFlow::Break(Err(ParseError::Unsupported(
                                    "Symbolic exponentiation".to_string(),
                                )))
                            }
                        };

                        let rterm = match r.visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(t)) => t,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        ControlFlow::Break(Ok(ReTerm::Pow(Box::new(rterm), exp as usize)))
                    }
                    StringOp::ReLoop(indices, re) => {
                        let lower = match indices[0].as_ref() {
                            smt2parser::visitors::Index::Numeral(n) => match biguint2isize(n) {
                                Ok(i) => i,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            },
                            smt2parser::visitors::Index::Symbol(_) => {
                                return ControlFlow::Break(Err(ParseError::Unsupported(
                                    "Symbolic exponentiation".to_string(),
                                )))
                            }
                        };
                        let upper = match indices[1].as_ref() {
                            smt2parser::visitors::Index::Numeral(n) => match biguint2isize(n) {
                                Ok(i) => i,
                                Err(e) => return ControlFlow::Break(Err(e)),
                            },
                            smt2parser::visitors::Index::Symbol(_) => {
                                return ControlFlow::Break(Err(ParseError::Unsupported(
                                    "Symbolic exponentiation".to_string(),
                                )))
                            }
                        };
                        let rterm = match re.visit_with(self) {
                            ControlFlow::Continue(_) => unreachable!(),
                            ControlFlow::Break(Ok(t)) => t,
                            ControlFlow::Break(Err(e)) => return ControlFlow::Break(Err(e)),
                        };
                        ControlFlow::Break(Ok(ReTerm::Loop(
                            Box::new(rterm),
                            lower as usize,
                            upper as usize,
                        )))
                    }
                    StringOp::StrConcat(_)
                    | StringOp::Len(_)
                    | StringOp::LexOrd(_)
                    | StringOp::InRe(_, _)
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
                    | StringOp::IsDigit(_)
                    | StringOp::ToCode(_)
                    | StringOp::FromCode(_)
                    | StringOp::ToInt(_)
                    | StringOp::FromInt(_) => ControlFlow::Break(Err(ParseError::Unsupported(
                        "String operation".to_string(),
                    ))),
                },
                Op::Arith(_) | Op::Array(_) | Op::BitVec(_) | Op::Set(_) => {
                    ControlFlow::Break(Err(ParseError::Unsupported(format!(
                        "3Non-String operation: {}",
                        s
                    ))))
                }
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(format!(
                    "4Non-String operation: {}",
                    term
                ))))
            }
        }
    }
}

fn biguint2isize(n: &BigUint) -> Result<isize, ParseError> {
    let as_isize: Result<isize, _> = n.try_into();
    match as_isize {
        Ok(i) => Ok(i),
        Err(_) => Err(ParseError::SyntaxError(format!(
            "Integer constant out of range: {}",
            n
        ))),
    }
}

struct IntArithTermBuilder<'a> {
    instance: &'a Instance,
}

impl<'a> Visitor<ALL> for IntArithTermBuilder<'a> {
    type BreakTy = Result<IntTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                Op::Arith(arith_op) => match arith_op {
                    ArithOp::Plus(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
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
                            lhs = IntTerm::plus(&lhs, &rhs);
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    ArithOp::Neg(t) => match t.visit_with(self) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(p)) => ControlFlow::Break(Ok(IntTerm::neg(&p))),
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    },
                    ArithOp::Minus(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
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
                            lhs = IntTerm::plus(&lhs, &rhs.neg());
                        }
                        ControlFlow::Break(Ok(lhs))
                    }
                    ArithOp::Mul(ts) => {
                        if ts.len() < 2 {
                            return ControlFlow::Break(Err(ParseError::SyntaxError(
                                "+ needs at least two arguments".to_string(),
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
                            lhs = IntTerm::times(&lhs, &rhs);
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
                Op::String(StringOp::Len(ts)) => {
                    let mut builder = StringLenToArithBuilder {
                        instance: self.instance,
                    };
                    match ts.visit_with(&mut builder) {
                        ControlFlow::Continue(_) => unreachable!(),
                        ControlFlow::Break(Ok(p)) => ControlFlow::Break(Ok(p)),
                        ControlFlow::Break(Err(e)) => ControlFlow::Break(Err(e)),
                    }
                }
                Op::String(_) | Op::Array(_) | Op::BitVec(_) | Op::Set(_) => ControlFlow::Break(
                    Err(ParseError::Unsupported(format!("Non-Int operation: {}", s))),
                ),
            },
            Term::CoreOp(_) | Term::UF(_) | Term::Let(_) | Term::Match(_) | Term::Quantifier(_) => {
                ControlFlow::Break(Err(ParseError::Unsupported(format!(
                    "Non-Int operation: {}",
                    term
                ))))
            }
        }
    }

    fn visit_const(&mut self, constant: &IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            Constant::Numeral(n) => {
                let as_isize: Result<isize, _> = n.try_into();
                match as_isize {
                    Ok(i) => ControlFlow::Break(Ok(IntTerm::constant(i))),
                    Err(_) => ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                        "Integer constant out of range: {}",
                        n
                    )))),
                }
            }
            Constant::String(_)
            | Constant::Decimal(_)
            | Constant::Hexadecimal(_)
            | Constant::Binary(_) => ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                "Expected numeral constant but found {}",
                constant
            )))),
        }
    }

    fn visit_var(&mut self, var: &IVar<<ALL as Logic>::Var>) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.instance.var_by_name(name) {
            if vvar.sort() != NSort::Int {
                return ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                    "Expected int variable but found {} ",
                    vvar.sort()
                ))));
            }
            ControlFlow::Break(Ok(IntTerm::var(vvar)))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

pub struct StringLenToArithBuilder<'a> {
    instance: &'a Instance,
}

impl<'a> Visitor<ALL> for StringLenToArithBuilder<'a> {
    type BreakTy = Result<IntTerm, ParseError>;

    fn visit_term(&mut self, term: &Term<ALL>) -> ControlFlow<Self::BreakTy> {
        match term {
            Term::Constant(c) => c.visit_with(self),
            Term::Variable(v) => v.visit_with(self),

            Term::OtherOp(s) => match s.as_ref() {
                Op::String(sop) => match sop {
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
                                ControlFlow::Break(Ok(p)) => lhs = IntTerm::plus(&lhs, &p),
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
                Op::Arith(_) | Op::Array(_) | Op::BitVec(_) | Op::Set(_) => {
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

    fn visit_const(&mut self, constant: &IConst) -> ControlFlow<Self::BreakTy> {
        match constant.as_ref() {
            Constant::String(s) => {
                ControlFlow::Break(Ok(IntTerm::Const(s.chars().count() as isize)))
            }
            Constant::Numeral(_)
            | Constant::Decimal(_)
            | Constant::Hexadecimal(_)
            | Constant::Binary(_) => ControlFlow::Break(Err(ParseError::Unsupported(format!(
                "Expected string term but found {}",
                constant
            )))),
        }
    }

    fn visit_var(&mut self, var: &IVar<<ALL as Logic>::Var>) -> ControlFlow<Self::BreakTy> {
        let name = var.as_ref().sym_str();
        if let Some(vvar) = self.instance.var_by_name(name) {
            if vvar.sort() != NSort::String {
                return ControlFlow::Break(Err(ParseError::SyntaxError(format!(
                    "Expected string variable but found {} ",
                    vvar.sort()
                ))));
            }
            ControlFlow::Break(Ok(IntTerm::Var(vvar.len_var().unwrap())))
        } else {
            ControlFlow::Break(Err(ParseError::UnknownIdentifier(name.to_string())))
        }
    }
}

fn isort2sort(sort: &ISort) -> Result<NSort, ParseError> {
    match sort.as_ref() {
        Sort::Simple { identifier } => match identifier.as_ref() {
            Identifier::Simple { symbol } => match symbol.0.to_lowercase().as_str() {
                "string" => Ok(NSort::String),
                "int" => Ok(NSort::Int),
                "bool" => Ok(NSort::Bool),
                _ => Err(ParseError::Unsupported(format!("Sort {}", symbol.0))),
            },
            Identifier::Indexed { symbol, .. } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
        },
        Sort::Parameterized { identifier, .. } => match identifier.as_ref() {
            Identifier::Simple { symbol } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
            Identifier::Indexed { symbol, .. } => {
                Err(ParseError::Unsupported(format!("Sort {}", symbol.0)))
            }
        },
    }
}
