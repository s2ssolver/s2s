use std::cmp::min;

use crate::{
    formula::{Atom, Formula, Predicate},
    model::words::WordEquation,
};

/// Strips the longest common prefix from both sides of the given word equation and returns the result.
fn strip_prefix(weq: &WordEquation) -> WordEquation {
    let mut i = 0;
    let n = weq.lhs().length();
    let m = weq.rhs().length();
    while i < min(n, m) {
        if weq.lhs()[i] != weq.rhs()[i] {
            break;
        }
        i += 1;
    }
    return WordEquation::new(
        weq.lhs().factor(i, n).unwrap(),
        weq.rhs().factor(i, m).unwrap(),
    );
}

/// Strips the longest common suffix from both sides of the given word equation and returns the result.
fn strip_suffix(weq: &WordEquation) -> WordEquation {
    strip_prefix(&weq.reverse()).reverse()
}

/// Strips the longest common prefix and suffix from both sides of the given word equation and returns the result.
fn strip(weq: &WordEquation) -> WordEquation {
    strip_suffix(&strip_prefix(weq))
}

/// Preprocesses the given word equation by stripping the longest common prefix and suffix from both sides.
fn preprocess_word_equation(weq: &WordEquation) -> WordEquation {
    strip(weq)
}

fn preprocess_predicate(pred: &Predicate) -> Predicate {
    match pred {
        Predicate::WordEquation(weq) => {
            let preprocessed = preprocess_word_equation(weq);
            Predicate::WordEquation(preprocessed)
        }
        Predicate::RegulaConstraint(_, _) => pred.clone(),
    }
}

/* Todo: Activate/Deactivate preprocessing steps using structs of traits {Formula Preprocessor, Predicate Preprocessor}
 * Todo: Add more preprocessing steps:
 * - Collapse nested And/Or
 * - Remove duplicate atoms from And/Or
 * - Collapse double negation
 * - Convert to nnf
 */

/// Preprocesses the given formula
pub fn preprocess(formula: &Formula) -> Formula {
    match formula {
        Formula::True => todo!(),
        Formula::False => todo!(),
        Formula::Atom(a) => Formula::Atom(match a {
            Atom::Predicate(p) => Atom::Predicate(preprocess_predicate(p)),
            Atom::BoolVar(v) => Atom::BoolVar(*v),
        }),
        Formula::Or(f) => Formula::Or(f.iter().map(|t| preprocess(t)).collect()),
        Formula::And(f) => Formula::And(f.iter().map(|t| preprocess(t)).collect()),
        Formula::Not(f) => Formula::Not(Box::new(preprocess(f.as_ref()))),
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn test_strip_const_prefix_no_match() {
        let weq = WordEquation::constant("foo", "bar");
        let stripped = strip_prefix(&weq);
        assert_eq!(stripped, WordEquation::constant("foo", "bar"));
    }

    #[test]
    fn test_strip_const_prefix_match() {
        let weq = WordEquation::constant("foofoo", "foobar");
        let stripped = strip_prefix(&weq);
        assert_eq!(stripped, WordEquation::constant("foo", "bar"));
    }

    #[test]
    fn test_strip_prefix_eq() {
        let weq = WordEquation::constant("foo", "foo");
        let stripped = strip_prefix(&weq);
        assert_eq!(stripped, WordEquation::constant("", ""));
    }

    #[quickcheck]
    fn strip_prefix_returns_suffix(weq: WordEquation) -> bool {
        let stripped = strip_prefix(&weq);
        weq.lhs().ends_with(&stripped.lhs()) && weq.rhs().ends_with(&stripped.rhs())
    }

    #[quickcheck]
    fn strip_suffix_returns_prefix(weq: WordEquation) -> bool {
        let stripped = strip_suffix(&weq);
        weq.lhs().starts_with(&stripped.lhs()) && weq.rhs().starts_with(&stripped.rhs())
    }
}
