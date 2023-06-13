//! Provides types and functions for propositional logic and SAT solving

use std::sync::atomic::{AtomicU32, Ordering};

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
