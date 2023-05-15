use std::fmt::Display;

use indexmap::IndexSet;

use crate::sat::{as_lit, neg, pvar, Cnf, PLit, PVar};

use super::EncodingResult;

pub fn exactly_one(vars: &[PVar]) -> Cnf {
    eo_naive(vars)
}

pub fn amo(vars: &[PVar]) -> Cnf {
    amo_binomial(vars)
}

/// Naive encoding of at least one and at most one constraints.
/// Needs quadratic number of clauses.
fn eo_naive(vars: &[PVar]) -> Cnf {
    let mut cnf = Cnf::new();
    // At least one
    let as_lits: Vec<PLit> = vars.iter().copied().map(as_lit).collect();
    cnf.push(as_lits.clone());
    // At most one
    for (i, x) in as_lits.iter().enumerate() {
        for y in as_lits.iter().skip(i + 1) {
            cnf.push(vec![-(*x), -(*y)]);
        }
    }
    cnf
}

fn amo_binomial(vars: &[PVar]) -> Cnf {
    let mut cnf = Cnf::new();
    let as_lits: Vec<PLit> = vars.iter().copied().map(as_lit).collect();
    for (i, x) in as_lits.iter().enumerate() {
        for y in as_lits.iter().skip(i + 1) {
            cnf.push(vec![-(*x), -(*y)]);
        }
    }
    cnf
}

/// Incremental encoding of at most one constraints.
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
        let as_lits_old: Vec<PLit> = self.vars.iter().copied().map(as_lit).collect();
        let as_lits_new: Vec<PLit> = vars.iter().copied().map(as_lit).collect();
        for x in as_lits_old.iter() {
            for y in as_lits_new.iter() {
                cnf.push(vec![-(*x), -(*y)]);
            }
        }
        self.vars.extend(vars);
        EncodingResult::cnf(cnf)
    }
}

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
        let mut clause = [neg(selector)].to_vec();
        clause.extend(self.vars.iter().copied().map(as_lit));
        cnf.push(clause);

        if let Some(old_selector) = self.selector {
            cnf.push(vec![neg(old_selector)]);
        }
        self.selector = Some(selector);
        let assm = IndexSet::from([as_lit(self.selector.unwrap())]);
        EncodingResult::Cnf(cnf, assm)
    }
}

#[derive(Default)]
pub struct IncrementalEO {
    amo: IncrementalAMO,
    alo: IncrementalALO,
}

impl IncrementalEO {
    pub fn new() -> Self {
        Self {
            amo: IncrementalAMO::new(),
            alo: IncrementalALO::new(),
        }
    }

    pub fn add(&mut self, vars: &[PVar]) -> EncodingResult {
        let mut amo = self.amo.add(vars);
        let alo = self.alo.add(vars);
        amo.join(alo);
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

    use super::*;
    #[test]
    fn test_eo_naive_encoding() {
        let cnf = eo_naive(&[1, 2, 3]);
        assert_eq!(
            cnf,
            vec![
                vec![1, 2, 3], // At least one
                vec![-1, -2],  // At most one
                vec![-1, -3],
                vec![-2, -3],
            ]
        );
    }

    #[quickcheck]
    fn test_eo_naive_correct(vars: Vec<u8>) -> TestResult {
        let vars: Vec<_> = vars.iter().map(|x| *x as PVar + 1).unique().collect();
        if vars.len() < 2 {
            return TestResult::discard();
        }
        let cnf = eo_naive(&vars);
        let mut solver: cadical::Solver = cadical::Solver::new();
        for clause in cnf {
            solver.add_clause(clause);
        }
        assert!(matches!(solver.solve(), Some(true)));
        let ts = vars
            .iter()
            .map(|x| solver.value(*x as PLit).unwrap())
            .filter(|x| *x)
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
        let mut solver: cadical::Solver = cadical::Solver::new();

        match cnf {
            EncodingResult::Cnf(cnf, assm) => {
                for clause in cnf {
                    solver.add_clause(clause);
                }
                assert!(matches!(solver.solve_with(assm.into_iter()), Some(true)));
                let ts = vars
                    .iter()
                    .map(|x| solver.value(*x as PLit).unwrap())
                    .filter(|x| *x)
                    .count();
                TestResult::from_bool(ts == 1)
            }
            EncodingResult::Trivial(_) => unreachable!(),
        }
    }
}
