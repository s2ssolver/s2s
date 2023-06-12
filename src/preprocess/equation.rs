use std::cmp::min;

use crate::model::words::{Symbol, WordEquation};

use super::PreprocessingResult;

/// Preprocesses the given word equation by stripping the longest common prefix and suffix from both sides.
pub fn preprocess_word_equation(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    // Strip longest common constant prefix / suffix
    let mut preprocessed = strip(weq);

    // Check constant prefix/suffix matching
    preprocessed = preprocessed.and_then(|eq| match_const_prefix_suffix(&eq));

    // Check Parikh matrix

    //Check factorization

    // Reduce trivial cases
    preprocessed = preprocessed.and_then(|eq| reduce_trivial(&eq));

    if let PreprocessingResult::Changed(sripped) = &preprocessed {
        log::debug!("Stripped {} to {}", weq, sripped);
    }
    preprocessed
}

/// Strips the longest common prefix from both sides of the given word equation and returns the result.
fn strip_prefix(weq: &WordEquation) -> PreprocessingResult<WordEquation> {
    let mut i = 0;
    let n = weq.lhs().length();
    let m = weq.rhs().length();
    while i < min(n, m) {
        if weq.lhs()[i] != weq.rhs()[i] {
            break;
        }
        i += 1;
    }

    let lhs_new = weq.lhs().factor(i, n).unwrap();
    let rhs_new = weq.rhs().factor(i, m).unwrap();

    if i == 0 {
        PreprocessingResult::Unchanged
    } else {
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
    } else if weq.lhs().is_empty() ^ weq.rhs().is_empty() {
        return PreprocessingResult::False;
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
        PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
        PreprocessingResult::Changed(w) => strip_suffix(&weq),
        PreprocessingResult::False => PreprocessingResult::False,
        PreprocessingResult::True => PreprocessingResult::True,
    }
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
