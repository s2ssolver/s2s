use crate::sat::{neg, Cnf, PLit, PVar};

pub fn exactly_one(lits: &[PLit]) -> Cnf {
    eo_naive(lits)
}

/// Naive encoding of at least one and at most one constraints.
/// Needs quadratic number of clauses.
fn eo_naive(list: &[PLit]) -> Cnf {
    let mut cnf = Cnf::new();
    // At least one
    cnf.push(list.to_vec());
    // At most one
    for (i, x) in list.iter().enumerate() {
        for y in list.iter().skip(i + 1) {
            cnf.push(vec![-(*x), -(*y)]);
        }
    }
    cnf
}

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
