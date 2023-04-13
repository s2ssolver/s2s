use crate::sat::{as_lit, Cnf, PLit, PVar};

pub fn exactly_one(lits: &[PVar]) -> Cnf {
    eo_naive(lits)
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
}
