//! Contains facilities for encoding cardinality constraints into SAT.

use std::fmt::Display;

use indexmap::IndexSet;
use rustsat::{instances::Cnf, types::Clause};

use crate::sat::{nlit, plit, pvar, PVar};

use super::EncodingResult;

/// At least one encoding of the given variables.
///
/// Returns a CNF encoding of the constraint that at least one and at most one of the given variables is true.
pub fn exactly_one(vars: &[PVar]) -> Cnf {
    eo_naive(vars)
}

/// At most one encoding
#[allow(unused)]
pub fn amo(vars: &[PVar]) -> Cnf {
    amo_binomial(vars)
}

/// Naive encoding of at least one and at most one constraints.
/// Needs quadratic number of clauses.
fn eo_naive(vars: &[PVar]) -> Cnf {
    let mut cnf = Cnf::new();
    // At least one
    let as_lits: Clause = vars.iter().copied().map(plit).collect();
    cnf.add_clause(as_lits.clone());
    // At most one
    for (i, x) in as_lits.iter().enumerate() {
        for y in as_lits.iter().skip(i + 1) {
            cnf.add_binary(-(*x), -(*y));
        }
    }
    cnf
}

/// Binomial (i.e. naive pairwise) encoding of at most one constraints.
fn amo_binomial(vars: &[PVar]) -> Cnf {
    let mut cnf = Cnf::new();
    let as_lits: Clause = vars.iter().copied().map(plit).collect();
    for (i, x) in as_lits.iter().enumerate() {
        for y in as_lits.iter().skip(i + 1) {
            cnf.add_binary(-(*x), -(*y));
        }
    }
    cnf
}

/// Incremental encoder of at most one constraints.
///
/// This encoding is incremental in the sense that it can be extended with new variables.
#[derive(Default)]
pub struct IncrementalAMO {
    vars: Vec<PVar>,
}

impl IncrementalAMO {
    pub fn new() -> Self {
        Self { vars: vec![] }
    }

    /// Adds new variables to the encoding
    pub fn add(&mut self, vars: &[PVar]) -> EncodingResult {
        // Encode binomial AMO:
        let mut cnf = Cnf::new();
        // At most one of the new ones
        cnf.extend(amo_binomial(vars));

        // At most one between the old and the new ones
        let as_lits_old: Clause = self.vars.iter().copied().map(plit).collect();
        let as_lits_new: Clause = vars.iter().copied().map(plit).collect();
        for x in as_lits_old.iter() {
            for y in as_lits_new.iter() {
                cnf.add_binary(-(*x), -(*y));
            }
        }
        self.vars.extend(vars);
        EncodingResult::cnf(cnf)
    }
}

/// Incremental encoder of at most one constraints.
///
/// This encoding is incremental in the sense that it can be extended with new variables.
#[derive(Default)]
pub struct IncrementalALO {
    vars: Vec<PVar>,
    selector: Option<PVar>,
}

impl IncrementalALO {
    pub fn new() -> Self {
        Self {
            vars: vec![],
            selector: None,
        }
    }

    /// Adds new variables to the encoding
    pub fn add(&mut self, vars: &[PVar]) -> EncodingResult {
        // Encode binomial AMO:
        let mut cnf = Cnf::new();
        self.vars.extend(vars);
        let selector = pvar();
        let mut clause: Clause = [nlit(selector)].into();
        clause.extend(self.vars.iter().copied().map(plit));
        cnf.add_clause(clause);

        if let Some(old_selector) = self.selector {
            cnf.add_unit(nlit(old_selector));
        }
        self.selector = Some(selector);
        let assm = IndexSet::from([plit(self.selector.unwrap())]);
        EncodingResult::Cnf(cnf, assm)
    }
}

/// Incremental encoder of exactly one constraints.
///
/// This encoding is incremental in the sense that it can be extended with new variables.
#[derive(Default)]
pub struct IncrementalEO {
    amo: IncrementalAMO,
    alo: IncrementalALO,
}

impl IncrementalEO {
    #[allow(unused)]
    pub fn new() -> Self {
        Self {
            amo: IncrementalAMO::new(),
            alo: IncrementalALO::new(),
        }
    }

    pub fn add(&mut self, vars: &[PVar]) -> EncodingResult {
        let mut amo = self.amo.add(vars);
        let alo = self.alo.add(vars);
        amo.extend(alo);
        amo
    }
}

impl Display for IncrementalEO {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Exactly one of: {:?}", self.alo.vars)
    }
}

#[cfg(test)]
mod tests {

    use itertools::Itertools;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use rustsat::solvers::{Solve, SolveIncremental, SolverResult};
    use rustsat::types::TernaryVal;
    use rustsat_cadical::CaDiCaL;

    use super::*;
    #[test]
    fn test_eo_naive_encoding() {
        let cnf = eo_naive(&[1, 2, 3]);
        let mut expected = Cnf::new();
        expected.add_clause([plit(1), plit(2), plit(3)].into()); // At least one
        expected.add_clause([nlit(1), nlit(2)].into()); // At most one
        expected.add_clause([nlit(1), nlit(3)].into());
        expected.add_clause([nlit(2), nlit(3)].into());
        assert_eq!(cnf, expected,);
    }

    #[quickcheck]
    fn test_eo_naive_correct(vars: Vec<u8>) -> TestResult {
        let vars: Vec<_> = vars.iter().map(|x| *x as PVar + 1).unique().collect();
        if vars.len() < 2 {
            return TestResult::discard();
        }
        let cnf = eo_naive(&vars);
        let mut solver = CaDiCaL::default();
        solver.add_cnf(cnf).unwrap();

        assert!(matches!(solver.solve(), Ok(SolverResult::Sat)));
        let solution = solver.full_solution().unwrap();
        let ts = vars
            .iter()
            .map(|x| solution.lit_value(plit(*x)))
            .filter(|x| matches!(x, TernaryVal::True))
            .count();
        TestResult::from_bool(ts == 1)
    }

    #[quickcheck]
    fn test_incremental_eo_naive_correct(vars: Vec<u8>) -> TestResult {
        let vars: Vec<_> = vars.iter().map(|x| *x as PVar + 1).unique().collect();
        if vars.len() < 2 {
            return TestResult::discard();
        }
        let mut eo_encoder = IncrementalEO::new();
        let cnf = eo_encoder.add(&vars);
        let mut solver = CaDiCaL::default();

        match cnf {
            EncodingResult::Cnf(cnf, assm) => {
                solver.add_cnf(cnf).unwrap();
                let assm = assm.into_iter().collect_vec();
                let res = solver.solve_assumps(&assm).unwrap();
                assert!(matches!(res, SolverResult::Sat));
                let solution = solver.full_solution().unwrap();
                let ts = vars
                    .iter()
                    .map(|x| solution.lit_value(plit(*x)))
                    .filter(|x| matches!(x, TernaryVal::True))
                    .count();
                TestResult::from_bool(ts == 1)
            }
            EncodingResult::Trivial(_) => unreachable!(),
        }
    }
}
