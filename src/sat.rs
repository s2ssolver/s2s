//! Provides types and functions for propositional logic and SAT solving

use std::sync::atomic::{AtomicU32, Ordering};

use indexmap::IndexMap;

use crate::{
    error::Error,
    model::{
        formula::{Atom, Formula},
        Sort, VarManager, Variable,
    },
};

/// A global counter for propositional variables.
/// The counter is used to generate new propositional variables.
/// It is incremented whenever a new variable is generated using [pvar()].
static PVAR_COUNTER: AtomicU32 = AtomicU32::new(1);

/// A propositional variable
pub type PVar = u32;
/// A propositional literal, i.e., a variable or its negation
pub type PLit = i32;
/// A clause, i.e., a disjunction of literals
pub type Clause = Vec<PLit>;
/// A formula in conjunctive normal form, i.e., a conjunction of clauses
pub type Cnf = Vec<Clause>;

pub fn neg(var: PVar) -> PLit {
    -as_lit(var)
}
pub fn as_lit(var: PVar) -> PLit {
    var as i32
}

/// Creates and returns a new unused propositional variable.
/// The first variable is always 1. All following variables are consecutive numbers.
/// This function is thread-safe and guaranteed to return unique variables.
///
/// # Panics
/// Panics if the number of propositional variables exceeds the maximum value of `i32`.
pub fn pvar() -> PVar {
    let v = PVAR_COUNTER.fetch_add(1, Ordering::SeqCst);
    if v > i32::MAX as u32 {
        panic!("Too many propositional variables")
    }
    v as PVar
}

/// Converts the given formula to conjunctive normal form using the Tseitin transformation.
/// Uses the given mapping to map [Variable]s of sort `Bool` to propositional variables [PVar].
///
/// This implementation is based on the "Handbook of Automated Reasoning" by J. Harrison.
///
/// # Errors
/// Returns an error if
/// - the formula contains a variable that is not mapped to a propositional variable
/// - the formula contains a variable that is mapped to a propositional variable of a different sort
/// - the formula is not propositional
/// - the formula is not in negation normal form
pub fn to_cnf(formula: &Formula, var_manager: &mut VarManager) -> Result<Cnf, Error> {
    fn maincnf(
        fm: &Formula,
        defs: &mut IndexMap<Formula, Variable>,
        var_manager: &mut VarManager,
    ) -> Result<Formula, Error> {
        match fm {
            Formula::And(fs) | Formula::Or(fs) => {
                if fs.is_empty() {
                    Ok(Formula::ffalse())
                } else if fs.len() == 1 {
                    maincnf(&fs[0], defs, var_manager)
                } else {
                    defstep(fm, defs, var_manager)
                }
            }
            Formula::Not(nf) => match nf.as_ref() {
                Formula::Atom(Atom::BoolVar(_)) => Ok(fm.clone()),
                Formula::Atom(Atom::Predicate(_)) => Err(Error::EncodingError(
                    "Formula not propositional".to_string(),
                )),
                _ => Err(Error::EncodingError("Not in NNF".to_string())),
            },
            Formula::Atom(Atom::Predicate(_)) => Err(Error::EncodingError(
                "Formula not propositional".to_string(),
            )),
            _ => Ok(fm.clone()),
        }
    }

    fn defstep(
        fm: &Formula,
        defs: &mut IndexMap<Formula, Variable>,
        var_manager: &mut VarManager,
    ) -> Result<Formula, Error> {
        match fm {
            Formula::And(fs) | Formula::Or(fs) => {
                let mut res = Vec::with_capacity(fs.len());
                for f in fs {
                    res.push(maincnf(f, defs, var_manager)?);
                }
                let res_fm = if matches!(fm, Formula::And(_)) {
                    Formula::and(res)
                } else if matches!(fm, Formula::Or(_)) {
                    Formula::or(res)
                } else {
                    unreachable!()
                };
                match defs.get(&res_fm) {
                    Some(v) => Ok(Formula::boolvar(v.clone())),
                    None => {
                        let v = var_manager.tmp_var(Sort::Bool);
                        defs.insert(res_fm, v.clone());
                        Ok(Formula::boolvar(v))
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    let mut defs = IndexMap::new();

    let res: Formula = maincnf(formula, &mut defs, var_manager)?;
    let mut cnf = Cnf::new();
    // TODO: Move to function `cnf_to_clauses(fm: &Formula) -> Result<Cnf, Error>`
    match res {
        Formula::Atom(Atom::True) => (),
        Formula::Atom(Atom::False) => cnf.push(vec![]),
        Formula::Atom(Atom::BoolVar(x)) => {
            if let Variable::Bool { value, .. } = x {
                cnf.push(vec![as_lit(value)]);
            } else {
                panic!("Variable is not a boolean variable")
            }
        }
        Formula::Or(fs) => {
            let mut clause = Vec::with_capacity(fs.len());
            for f in fs {
                if let Formula::Atom(Atom::BoolVar(Variable::Bool { value, .. })) = f {
                    clause.push(as_lit(value));
                } else {
                    unreachable!()
                }
            }
            cnf.push(clause);
        }
        Formula::And(fs) => {
            for disj in fs {
                match disj {
                    Formula::Atom(Atom::True) => (),
                    Formula::Atom(Atom::False) => cnf.push(vec![]),
                    Formula::Atom(Atom::BoolVar(x)) => {
                        if let Variable::Bool { value, .. } = x {
                            cnf.push(vec![as_lit(value)]);
                        } else {
                            unreachable!()
                        }
                    }
                    Formula::Not(f) => {
                        if let Formula::Atom(Atom::BoolVar(Variable::Bool { value, .. })) =
                            f.as_ref()
                        {
                            cnf.push(vec![neg(*value)]);
                        } else {
                            unreachable!()
                        }
                    }
                    Formula::Or(fs) => {
                        let mut clause = Vec::with_capacity(fs.len());
                        for f in fs {
                            if let Formula::Atom(Atom::BoolVar(Variable::Bool { value, .. })) = f {
                                clause.push(as_lit(value));
                            } else {
                                unreachable!()
                            }
                        }
                        cnf.push(clause);
                    }
                    Formula::Atom(Atom::Predicate(_)) => unreachable!(),
                    Formula::And(_) => unreachable!(),
                }
            }
        }
        Formula::Not(_) => unreachable!(),
        Formula::Atom(Atom::Predicate(_)) => unreachable!(),
    }
    Ok(cnf)
}

#[cfg(test)]
mod tests {

    use quickcheck_macros::quickcheck;
    use serial_test::serial;

    use super::*;

    #[quickcheck]
    #[serial]
    fn test_pvar_incremented(calls: u8) {
        for _ in 0..calls {
            let v = pvar();
            assert!(v < PVAR_COUNTER.load(Ordering::SeqCst));
            let v2 = pvar();
            assert!(v2 < PVAR_COUNTER.load(Ordering::SeqCst));
            assert!(v2 > v);
        }
    }

    #[test]
    fn test_neg() {
        let v = pvar();

        assert_eq!(neg(v), -(v as i32));
    }

    #[test]
    fn test_as_lit() {
        let v = pvar();
        assert_eq!(as_lit(v), v as i32);
    }
}
