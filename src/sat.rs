//! Provides types and functions for propositional logic and SAT solving

use std::sync::atomic::{AtomicU32, Ordering};

use indexmap::IndexMap;

use crate::{
    error::Error,
    instance::Instance,
    model::{
        formula::{Atom, Literal, NNFFormula},
        Sort, Variable,
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
pub fn to_cnf(formula: &NNFFormula, instance: &mut Instance) -> Result<Cnf, Error> {
    fn maincnf(
        fm: &NNFFormula,
        defs: &mut IndexMap<NNFFormula, Variable>,
        instance: &mut Instance,
    ) -> Result<NNFFormula, Error> {
        match fm {
            NNFFormula::And(fs) | NNFFormula::Or(fs) => {
                if fs.len() == 1 {
                    maincnf(&fs[0], defs, instance)
                } else {
                    defstep(fm, defs, instance)
                }
            }
            NNFFormula::Literal(lit) => {
                if matches!(lit.atom(), Atom::BoolVar(_)) {
                    Ok(fm.clone())
                } else {
                    Err(Error::EncodingError(
                        "Formula not propositional".to_string(),
                    ))
                }
            }
        }
    }

    fn defstep(
        fm: &NNFFormula,
        defs: &mut IndexMap<NNFFormula, Variable>,
        instance: &mut Instance,
    ) -> Result<NNFFormula, Error> {
        match fm {
            NNFFormula::And(fs) | NNFFormula::Or(fs) => {
                let mut res = Vec::with_capacity(fs.len());
                for f in fs {
                    res.push(maincnf(f, defs, instance)?);
                }
                let res_fm = if matches!(fm, NNFFormula::And(_)) {
                    NNFFormula::And(res)
                } else if matches!(fm, NNFFormula::Or(_)) {
                    NNFFormula::Or(res)
                } else {
                    unreachable!()
                };
                match defs.get(&res_fm) {
                    Some(v) => Ok(NNFFormula::boolvar(v.clone(), true)),
                    None => {
                        let v = Variable::temp(Sort::Bool);
                        instance.add_var(v.clone());
                        defs.insert(res_fm, v.clone());
                        Ok(NNFFormula::boolvar(v, true))
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    let mut defs = IndexMap::new();

    let res: NNFFormula = maincnf(formula, &mut defs, instance)?;
    let mut cnf = cnf_to_clause(&res);
    // TODO: Move to function `cnf_to_clauses(fm: &Formula) -> Result<Cnf, Error>`

    // Add definitional clauses
    for (f, d) in defs {
        let boolvar = if let Variable::Bool { value, .. } = d {
            value
        } else {
            unreachable!()
        };
        match f {
            NNFFormula::Or(fs) => {
                // d -> \/fs and \/fs -> d
                let mut clause = Vec::with_capacity(fs.len() + 1);
                clause.push(neg(boolvar));
                for f in fs {
                    match f {
                        NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                            value,
                            ..
                        }))) => {
                            clause.push(as_lit(value));
                            cnf.push(vec![neg(value), as_lit(boolvar)]);
                        }
                        NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                            value,
                            ..
                        }))) => {
                            clause.push(as_lit(value));
                            cnf.push(vec![as_lit(value), neg(boolvar)]);
                        }
                        _ => unreachable!(),
                    }
                }
                cnf.push(clause)
            }
            NNFFormula::And(fs) => {
                // d -> /\fs and /\fs -> d
                let mut clause = Vec::with_capacity(fs.len() + 1);
                clause.push(as_lit(boolvar));
                for f in fs {
                    match f {
                        NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                            value,
                            ..
                        }))) => {
                            clause.push(neg(value));
                            cnf.push(vec![neg(boolvar), as_lit(value)]);
                        }
                        NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                            value,
                            ..
                        }))) => {
                            clause.push(as_lit(value));
                            cnf.push(vec![neg(boolvar), neg(value)]);
                        }
                        _ => unreachable!(),
                    }
                }
                cnf.push(clause)
            }
            _ => unreachable!(),
        }
    }
    Ok(cnf)
}

/// Converts a formula in conjunctive normal form to a [Clause].
/// Panics if the formula is not in conjunctive normal form.
fn cnf_to_clause(fm: &NNFFormula) -> Cnf {
    let mut cnf = Cnf::new();
    match fm {
        NNFFormula::Literal(Literal::Neg(Atom::False))
        | NNFFormula::Literal(Literal::Pos(Atom::True)) => (),
        NNFFormula::Literal(Literal::Pos(Atom::False))
        | NNFFormula::Literal(Literal::Neg(Atom::True)) => cnf.push(vec![]),
        NNFFormula::Literal(Literal::Pos(a)) => match a {
            Atom::BoolVar(Variable::Bool { value, .. }) => {
                cnf.push(vec![as_lit(*value)]);
            }
            Atom::True => (),
            Atom::False => cnf.push(vec![]),
            _ => unreachable!(),
        },
        NNFFormula::Literal(Literal::Neg(a)) => match a {
            Atom::BoolVar(Variable::Bool { value, .. }) => {
                cnf.push(vec![neg(*value)]);
            }
            Atom::True => cnf.push(vec![]),
            Atom::False => (),
            _ => unreachable!(),
        },
        NNFFormula::Or(fs) => {
            let mut clause = Vec::with_capacity(fs.len());
            for f in fs {
                match f {
                    NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                        value,
                        ..
                    }))) => clause.push(as_lit(*value)),
                    NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                        value,
                        ..
                    }))) => clause.push(neg(*value)),
                    _ => panic!("Not a CNF formula"),
                }
            }
            cnf.push(clause);
        }
        NNFFormula::And(fs) => {
            for f in fs {
                match f {
                    NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                        value,
                        ..
                    }))) => cnf.push(vec![as_lit(*value)]),
                    NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                        value,
                        ..
                    }))) => cnf.push(vec![neg(*value)]),
                    NNFFormula::Or(_) => cnf.extend(cnf_to_clause(f)),
                    _ => panic!("Not a CNF formula"),
                }
            }
        }
    }
    cnf
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

    #[test]
    fn test_cnf_to_clause1() {
        // (A || B) && (!C || D || E)
        let fm = NNFFormula::And(vec![
            NNFFormula::Or(vec![
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 1,
                    name: "1".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 2,
                    name: "2".to_string(),
                }))),
            ]),
            NNFFormula::Or(vec![
                NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                    value: 3,
                    name: "3".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 4,
                    name: "4".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 5,
                    name: "5".to_string(),
                }))),
            ]),
        ]);

        let expected_cnf = vec![
            vec![as_lit(1), as_lit(2)],
            vec![neg(3), as_lit(4), as_lit(5)],
        ];

        assert_eq!(cnf_to_clause(&fm), expected_cnf);
    }

    #[test]
    #[should_panic]
    fn test_cnf_to_clause_not_cnf() {
        // Test case 2: CNF formula with base cases
        // (!F) && (A && B)
        let fm = NNFFormula::And(vec![
            NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                value: 1,
                name: "1".to_string(),
            }))),
            NNFFormula::And(vec![
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 2,
                    name: "2".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 3,
                    name: "3".to_string(),
                }))),
            ]),
        ]);

        cnf_to_clause(&fm);
    }

    #[test]
    fn test_cnf_to_clause_with_base() {
        // CNF formula with base cases
        // (A || B) /\ (C || D) /\ (!E) && (!F)
        let fm = NNFFormula::And(vec![
            NNFFormula::Or(vec![
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 1,
                    name: "1".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 2,
                    name: "2".to_string(),
                }))),
            ]),
            NNFFormula::Or(vec![
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 3,
                    name: "3".to_string(),
                }))),
                NNFFormula::Literal(Literal::Pos(Atom::BoolVar(Variable::Bool {
                    value: 4,
                    name: "4".to_string(),
                }))),
            ]),
            NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                value: 5,
                name: "5".to_string(),
            }))),
            NNFFormula::Literal(Literal::Neg(Atom::BoolVar(Variable::Bool {
                value: 6,
                name: "6".to_string(),
            }))),
        ]);

        let expected_cnf = vec![
            vec![as_lit(1), as_lit(2)],
            vec![as_lit(3), as_lit(4)],
            vec![neg(5)],
            vec![neg(6)],
        ];

        assert_eq!(cnf_to_clause(&fm), expected_cnf);
    }
}
