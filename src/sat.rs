//! Provides types and functions for propositional logic and SAT solving

use std::{
    fmt::Display,
    sync::atomic::{AtomicU32, Ordering},
};

use indexmap::IndexMap;
use rustsat::{
    instances::Cnf,
    types::{Clause, Lit},
};

/// A global counter for propositional variables.
/// The counter is used to generate new propositional variables.
/// It is incremented whenever a new variable is generated using [pvar()].
static PVAR_COUNTER: AtomicU32 = AtomicU32::new(1);

/// A propositional variable
pub type PVar = u32;

/// A propositional formula in negation normal form
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PFormula {
    And(Vec<PFormula>),
    Or(Vec<PFormula>),
    Lit(Lit),
}
impl PFormula {
    pub fn plit(var: PVar) -> Self {
        PFormula::Lit(plit(var))
    }

    pub fn nlit(var: PVar) -> Self {
        PFormula::Lit(nlit(var))
    }
}

impl Display for PFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PFormula::And(fs) => {
                write!(f, "(")?;
                for (i, fm) in fs.iter().enumerate() {
                    write!(f, "{}", fm)?;
                    if i < fs.len() - 1 {
                        write!(f, " && ")?;
                    }
                }
                write!(f, ")")
            }
            PFormula::Or(fs) => {
                write!(f, "(")?;
                for (i, fm) in fs.iter().enumerate() {
                    write!(f, "{}", fm)?;
                    if i < fs.len() - 1 {
                        write!(f, " || ")?;
                    }
                }
                write!(f, ")")
            }
            PFormula::Lit(l) => write!(f, "{}", l),
        }
    }
}

pub fn nlit(var: PVar) -> Lit {
    Lit::new(var, true)
}

pub fn plit(var: PVar) -> Lit {
    Lit::new(var, false)
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
pub fn to_cnf(formula: &PFormula) -> Cnf {
    fn maincnf(fm: &PFormula, defs: &mut IndexMap<PFormula, PVar>) -> PFormula {
        match fm {
            PFormula::And(fs) | PFormula::Or(fs) => {
                if fs.len() == 1 {
                    maincnf(&fs[0], defs)
                } else {
                    defstep(fm, defs)
                }
            }
            PFormula::Lit(_) => fm.clone(),
        }
    }

    fn defstep(fm: &PFormula, defs: &mut IndexMap<PFormula, PVar>) -> PFormula {
        match fm {
            PFormula::And(fs) | PFormula::Or(fs) => {
                let mut res = Vec::with_capacity(fs.len());
                for f in fs {
                    res.push(maincnf(f, defs));
                }
                let res_fm = if matches!(fm, PFormula::And(_)) {
                    PFormula::And(res)
                } else if matches!(fm, PFormula::Or(_)) {
                    PFormula::Or(res)
                } else {
                    unreachable!()
                };
                match defs.get(&res_fm) {
                    Some(v) => PFormula::plit(*v),
                    None => {
                        let v = pvar();
                        defs.insert(res_fm, v);
                        PFormula::plit(v)
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    if let Some(cnf) = cnf_to_clauses(formula) {
        return cnf;
    }

    let mut defs = IndexMap::new();

    let res: PFormula = maincnf(formula, &mut defs);
    let mut cnf = cnf_to_clauses(&res).unwrap();

    // Add definitional clauses
    for (f, def_var) in defs {
        match f {
            PFormula::Or(fs) => {
                // d -> \/fs and \/fs -> d
                let mut clause = Clause::with_capacity(fs.len() + 1);
                clause.add(nlit(def_var));
                for f in fs {
                    match f {
                        PFormula::Lit(val) => {
                            clause.add(val);
                            cnf.add_binary(-val, plit(def_var));
                        }
                        _ => unreachable!(),
                    }
                }
                cnf.add_clause(clause)
            }
            PFormula::And(fs) => {
                // d -> /\fs and /\fs -> d
                let mut clause = Clause::with_capacity(fs.len() + 1);
                clause.add(plit(def_var));
                for f in fs {
                    match f {
                        PFormula::Lit(val) => {
                            clause.add(-val);
                            cnf.add_binary(nlit(def_var), val);
                        }
                        _ => unreachable!(),
                    }
                }
                cnf.add_clause(clause)
            }
            _ => unreachable!(),
        }
    }
    cnf
}

/// Converts a formula in conjunctive normal form to a [Clause].
/// Panics if the formula is not in conjunctive normal form.
fn cnf_to_clauses(fm: &PFormula) -> Option<Cnf> {
    let mut cnf = Cnf::new();

    fn to_clause(lits: &[PFormula]) -> Option<Clause> {
        let mut clause = Clause::with_capacity(lits.len());
        for l in lits {
            if let PFormula::Lit(l) = l {
                clause.add(*l);
            } else {
                return None;
            }
        }
        Some(clause)
    }

    match fm {
        PFormula::Lit(v) => cnf.add_unit(*v),
        PFormula::Or(fs) => {
            cnf.add_clause(to_clause(fs)?);
        }
        PFormula::And(fs) => {
            for f in fs {
                match f {
                    PFormula::And(fs) => {
                        for f in fs {
                            let subcnf = cnf_to_clauses(f)?;
                            cnf.extend(subcnf);
                        }
                    }
                    PFormula::Or(fs) => {
                        cnf.add_clause(to_clause(fs)?);
                        (to_clause(fs));
                    }
                    PFormula::Lit(l) => cnf.add_unit(*l),
                }
            }
        }
    }
    Some(cnf)
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

        assert_eq!(nlit(v), Lit::negative(v));
        assert_eq!(nlit(v), -Lit::positive(v));
    }

    #[test]
    fn test_as_lit() {
        let v = pvar();
        assert_eq!(plit(v), Lit::positive(v));
        assert_eq!(plit(v), -Lit::negative(v));
    }

    #[test]
    fn test_cnf_to_clause1() {
        // (A || B) && (!C || D || E)
        let fm = PFormula::And(vec![
            PFormula::Or(vec![PFormula::plit(1), PFormula::plit(2)]),
            PFormula::Or(vec![
                PFormula::nlit(3),
                PFormula::plit(4),
                PFormula::plit(5),
            ]),
        ]);

        let mut expected_cnf = Cnf::with_capacity(2);
        expected_cnf.add_binary(plit(1), plit(2));
        expected_cnf.add_ternary(nlit(3), plit(4), plit(5));

        assert_eq!(cnf_to_clauses(&fm).unwrap(), expected_cnf);
    }

    #[test]
    fn test_cnf_to_clause_not_cnf() {
        // Test case 2: formula that is not in CNF
        // (!F) || (A && B)
        let fm = PFormula::Or(vec![
            PFormula::nlit(1),
            PFormula::And(vec![PFormula::plit(2), PFormula::plit(3)]),
        ]);

        assert!(cnf_to_clauses(&fm).is_none());
    }

    #[test]
    fn test_cnf_to_clause_with_base() {
        // CNF formula with base cases
        // (A || B) /\ (C || D) /\ (!E) && (!F)
        let fm = PFormula::And(vec![
            PFormula::Or(vec![PFormula::plit(1), PFormula::plit(2)]),
            PFormula::Or(vec![PFormula::plit(3), PFormula::plit(4)]),
            PFormula::nlit(5),
            PFormula::nlit(6),
        ]);

        let mut expected_cnf = Cnf::with_capacity(4);
        expected_cnf.add_binary(plit(1), plit(2));
        expected_cnf.add_binary(plit(3), plit(4));
        expected_cnf.add_unit(nlit(5));
        expected_cnf.add_unit(nlit(6));

        assert_eq!(cnf_to_clauses(&fm).unwrap(), expected_cnf);
    }
}
