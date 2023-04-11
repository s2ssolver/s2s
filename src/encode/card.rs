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

    use super::*;
    #[test]
    fn test_eo_naive() {
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

    // TODO use quickcheck to test arbitrary inputs with Cadical
}
