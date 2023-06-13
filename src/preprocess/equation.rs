use std::cmp::min;

use crate::model::words::{Symbol, WordEquation};

use super::PreprocessingResult;

/// Preprocesses the given word equation by stripping the longest common prefix and suffix from both sides.
pub fn preprocess_word_equation(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    // Strip longest common constant prefix / suffix
    let mut changed = false;
    let mut preprocessed = weq.clone();
    preprocessed = match strip(weq) {
        PreprocessingResult::Unchanged => preprocessed,
        PreprocessingResult::Changed(c) => {
            log::trace!("Stripping constants {} -> {}", preprocessed, c);
            changed = true;
            c
        }
        PreprocessingResult::False => return PreprocessingResult::False,
        PreprocessingResult::True => return PreprocessingResult::True,
    };

    // Check constant prefix/suffix matching
    preprocessed = match match_const_prefix_suffix(&preprocessed) {
        PreprocessingResult::Unchanged => preprocessed,
        PreprocessingResult::Changed(c) => {
            changed = true;
            c
        }
        PreprocessingResult::False => {
            log::trace!("Found mismatching constants: {}", preprocessed);
            return PreprocessingResult::False;
        }
        PreprocessingResult::True => return PreprocessingResult::True,
    };

    // Check Parikh matrix for suffixes
    //preprocessed = preprocessed.and_then(|eq| check_parikh(&eq));
    //log::trace!("After checking parikh {}", preprocessed);

    //Check factorization

    // Reduce trivial cases
    preprocessed = match reduce_trivial(&preprocessed) {
        PreprocessingResult::Unchanged => preprocessed.clone(),
        PreprocessingResult::Changed(c) => {
            changed = true;
            c
        }
        PreprocessingResult::False => {
            log::trace!("Reduced to false: {}", preprocessed);
            return PreprocessingResult::False;
        }
        PreprocessingResult::True => {
            log::trace!("Reduced to true: {}", preprocessed);
            return PreprocessingResult::True;
        }
    };

    if changed {
        PreprocessingResult::Changed(preprocessed)
    } else {
        PreprocessingResult::Unchanged
    }
}

/// Strips the longest common prefix from both sides of the given word equation and returns the result.
fn strip_prefix(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    let mut i = 0;
    let n = weq.lhs().len();
    let m = weq.rhs().len();
    while i < min(n, m) {
        if weq.lhs()[i] != weq.rhs()[i] {
            break;
        }

        i += 1;
    }

    if i == 0 {
        PreprocessingResult::Unchanged
    } else {
        let lhs_new = weq.lhs().factor(i, n).unwrap();
        let rhs_new = weq.rhs().factor(i, m).unwrap();

        let processed = WordEquation::new(lhs_new, rhs_new);

        PreprocessingResult::Changed(processed)
    }
}

/// Checks whether the patterns of the given word equation start and end with the same constant.
fn match_const_prefix_suffix(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    // Check if there is a mismatch in the first position
    if weq.lhs().is_empty() || weq.rhs().is_empty() {
        return PreprocessingResult::Unchanged;
    }
    if let (Some(Symbol::Constant(a)), Some(Symbol::Constant(b))) =
        (&weq.lhs().first(), &weq.rhs().first())
    {
        if a != b {
            return PreprocessingResult::False;
        }
    }

    if let (Some(Symbol::Constant(a)), Some(Symbol::Constant(b))) =
        (&weq.lhs().last(), &weq.rhs().last())
    {
        if a != b {
            return PreprocessingResult::False;
        }
    }

    PreprocessingResult::Unchanged
}

/// Checks whether the given word equation is trivially true or false.
fn reduce_trivial(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    if weq.lhs().is_empty() && weq.rhs().is_empty() {
        return PreprocessingResult::True;
    } else if weq.lhs().is_empty() {
        if weq.rhs().contains_constant() {
            return PreprocessingResult::False;
        } else {
            return PreprocessingResult::True;
        }
    } else if weq.rhs().is_empty() {
        if weq.lhs().contains_constant() {
            return PreprocessingResult::False;
        } else {
            return PreprocessingResult::True;
        }
    }

    PreprocessingResult::Unchanged
}

/// Strips the longest common suffix from both sides of the given word equation and returns the result.
fn strip_suffix(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    match strip_prefix(&weq.reverse()) {
        PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
        PreprocessingResult::Changed(w) => PreprocessingResult::Changed(w.reverse()),
        PreprocessingResult::False => PreprocessingResult::False,
        PreprocessingResult::True => PreprocessingResult::True,
    }
}

/// Strips the longest common prefix and suffix from both sides of the given word equation and returns the result.
fn strip(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    match strip_prefix(weq) {
        PreprocessingResult::Unchanged => strip_suffix(weq),
        PreprocessingResult::Changed(w) => match strip_suffix(&w) {
            PreprocessingResult::Unchanged => PreprocessingResult::Changed(w),
            PreprocessingResult::Changed(c) => PreprocessingResult::Changed(c),
            PreprocessingResult::False => PreprocessingResult::False,
            PreprocessingResult::True => PreprocessingResult::True,
        },
        PreprocessingResult::False => PreprocessingResult::False,
        PreprocessingResult::True => PreprocessingResult::True,
    }
}

/// Checks whether we can obtain suffixes by removing the prefix of the same length from both sides for which Parikk vectors of constants are equal, but the Parikh vectors of variables are not. In that case the equation has no solution.
#[allow(dead_code)]
fn check_parikh(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    let max = min(weq.lhs().len(), weq.rhs().len());
    let symbols = weq.symbols();
    for i in 0..max {
        let mut vars_align = true;
        let mut const_align = true;
        let lhs = weq.lhs().factor(i, weq.lhs().len()).unwrap();
        let rhs = weq.rhs().factor(i, weq.rhs().len()).unwrap();
        for s in &symbols {
            if lhs.count(s) != rhs.count(s) {
                if s.is_constant() {
                    const_align = false;
                } else {
                    vars_align = false;
                }
            }
        }
        if vars_align && !const_align {
            return PreprocessingResult::False;
        }
    }

    PreprocessingResult::Unchanged
}

#[cfg(test)]
mod tests {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn test_strip_const_prefix_no_match() {
        let weq = WordEquation::constant("foo", "bar");
        assert!(matches!(strip_prefix(&weq), PreprocessingResult::Unchanged));
    }

    #[test]
    fn test_strip_const_prefix_match() {
        let weq = WordEquation::constant("foofoo", "foobar");
        let stripped: PreprocessingResult<WordEquation> = strip_prefix(&weq);
        assert_eq!(
            stripped.as_option().unwrap(),
            &WordEquation::constant("foo", "bar")
        );
    }

    #[test]
    fn test_strip_prefix_eq() {
        let weq = WordEquation::constant("foo", "foo");
        let _empty = WordEquation::empty();

        assert!(matches!(
            strip_prefix(&weq),
            PreprocessingResult::Changed(_empty)
        ));
    }

    #[quickcheck]
    fn strip_prefix_returns_suffix(weq: WordEquation) -> bool {
        match strip_prefix(&weq) {
            PreprocessingResult::Changed(stripped) => {
                weq.lhs().ends_with(stripped.lhs()) && weq.rhs().ends_with(stripped.rhs())
            }
            _ => true,
        }
    }

    #[quickcheck]
    fn strip_suffix_returns_prefix(weq: WordEquation) -> bool {
        match strip_suffix(&weq) {
            PreprocessingResult::Changed(stripped) => {
                weq.lhs().starts_with(stripped.lhs()) && weq.rhs().starts_with(stripped.rhs())
            }
            _ => true,
        }
    }

    #[quickcheck]
    fn const_prefix_match(weq: WordEquation) -> TestResult {
        if weq.lhs().is_empty() || weq.rhs().is_empty() {
            return TestResult::discard();
        }
        match (&weq.lhs().first().unwrap(), &weq.rhs().first().unwrap()) {
            (Symbol::Constant(a), Symbol::Constant(b)) => {
                let res = if a == b {
                    match (&weq.lhs().last().unwrap(), &weq.rhs().last().unwrap()) {
                        (Symbol::Constant(a), Symbol::Constant(b)) => {
                            if a == b {
                                matches!(
                                    match_const_prefix_suffix(&weq),
                                    PreprocessingResult::Unchanged
                                )
                            } else {
                                matches!(
                                    match_const_prefix_suffix(&weq),
                                    PreprocessingResult::False
                                )
                            }
                        }
                        _ => return TestResult::discard(),
                    }
                } else {
                    matches!(match_const_prefix_suffix(&weq), PreprocessingResult::False)
                };
                TestResult::from_bool(res)
            }
            _ => TestResult::discard(),
        }
    }
}
