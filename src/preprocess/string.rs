use std::cmp::min;

use crate::model::{
    formula::{Formula, Predicate, Term},
    words::{StringTerm, Symbol, WordEquation},
    Substitution,
};

use super::{PreprocessingResult, Preprocessor};

pub struct WordEquationStripPrefixSuffix {}
pub struct WordEquationPrefixSuffixMatch {}
pub struct WordEquationParikhMatch {}
pub struct WordEquationFactorization {}
pub struct WordEquationTrivial {}
pub struct WordEquationFixedPrefixSuffix {}

/// Derives valid substitutions from word equations.
/// If applied, the resulting formula is equisatisfiable to the original one.
/// If the formula is asserted, i.e., always true, the found substitutions are valid for the whole formula.
pub struct WordEquationSubstitutions {}

impl WordEquationStripPrefixSuffix {
    /// Strips the longest common prefix from both sides of the given word equation and returns the result.
    fn strip_matches(eq: &WordEquation) -> Option<WordEquation> {
        // Convert to pattern, strip prefix, strip suffix, convert back
        let lhs = eq.lhs();
        let rhs = eq.rhs();

        let n = min(lhs.len(), rhs.len());
        let mut i = 0;
        while i < n && lhs[i] == rhs[i] {
            i += 1;
        }

        let mut j = 0;
        while j < n && lhs[(lhs.len() - 1) - j] == rhs[(rhs.len() - 1) - j] {
            j += 1;
        }

        if i == 0 && j == 0 {
            return None;
        } else {
            let lhs = lhs.factor(i, lhs.len() - j).unwrap();
            let rhs = rhs.factor(i, rhs.len() - j).unwrap();
            return Some(WordEquation::new(lhs, rhs));
        }
    }
}

impl Preprocessor for WordEquationStripPrefixSuffix {
    fn preprocess(&self, fm: &Formula) -> PreprocessingResult {
        match fm {
            Formula::Predicate(p) => match p {
                Predicate::Equality(Term::String(_), Term::String(_)) => {
                    if let Some(preprocessed) = Self::strip_matches(&p.clone().try_into().unwrap())
                    {
                        PreprocessingResult::Changed(preprocessed.into())
                    } else {
                        PreprocessingResult::Unchanged
                    }
                }
                _ => PreprocessingResult::Unchanged,
            },
            _ => PreprocessingResult::Unchanged,
        }
    }
}

impl WordEquationPrefixSuffixMatch {
    /// Checks whether the patterns of the given word equation start and end with the same constant.
    fn consts_match(weq: &WordEquation) -> bool {
        // Check if there is a mismatch in the first position
        if let (Some(Symbol::Constant(a)), Some(Symbol::Constant(b))) =
            (&weq.lhs().first(), &weq.rhs().first())
        {
            if a != b {
                return false;
            }
        }

        if let (Some(Symbol::Constant(a)), Some(Symbol::Constant(b))) =
            (&weq.lhs().last(), &weq.rhs().last())
        {
            if a != b {
                return false;
            }
        }

        true
    }
}

impl Preprocessor for WordEquationPrefixSuffixMatch {
    fn preprocess(&self, fm: &Formula) -> PreprocessingResult {
        match fm {
            Formula::Predicate(p) => match p {
                Predicate::Equality(Term::String(_), Term::String(_)) => {
                    if Self::consts_match(&p.clone().try_into().unwrap()) {
                        PreprocessingResult::Changed(Formula::False)
                    } else {
                        PreprocessingResult::Unchanged
                    }
                }
                _ => PreprocessingResult::Unchanged,
            },
            _ => PreprocessingResult::Unchanged,
        }
    }
}

impl WordEquationTrivial {
    /// Checks whether the given word equation is trivially true or false.
    fn is_trivial(weq: &WordEquation) -> Option<bool> {
        if weq.lhs().is_empty() && weq.rhs().is_empty() {
            Some(true)
        } else if weq.lhs().is_empty() {
            if weq.rhs().contains_constant() {
                Some(false)
            } else {
                Some(true)
            }
        } else if weq.rhs().is_empty() {
            if weq.lhs().contains_constant() {
                Some(false)
            } else {
                Some(true)
            }
        } else {
            None
        }
    }
}

impl Preprocessor for WordEquationTrivial {
    fn preprocess(&self, fm: &Formula) -> PreprocessingResult {
        match fm {
            Formula::Predicate(p) => match p {
                Predicate::Equality(Term::String(_), Term::String(_)) => {
                    match Self::is_trivial(&p.clone().try_into().unwrap()) {
                        Some(true) => PreprocessingResult::Changed(Formula::True),
                        Some(false) => PreprocessingResult::Changed(Formula::False),
                        None => PreprocessingResult::Unchanged,
                    }
                }
                _ => PreprocessingResult::Unchanged,
            },
            _ => PreprocessingResult::Unchanged,
        }
    }
}

impl WordEquationSubstitutions {
    fn derive_prefix_sub(eq: &WordEquation) -> Substitution {
        let mut subs = Substitution::new();
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        let sub_term = match (lhs.first(), rhs.first()) {
            (Some(Symbol::Variable(x)), None) | (None, Some(Symbol::Variable(x))) => {
                // x = ""
                Some((x, Term::String(StringTerm::empty())))
            }
            (Some(Symbol::Variable(x)), Some(_)) => {
                let next = match lhs.iter().skip(1).next() {
                    Some(Symbol::Variable(_)) => return subs, // Cannot infer anything
                    Some(Symbol::Constant(c)) => Some(*c),
                    None => None,
                };
                let mut pref = vec![];
                let mut rhs_iter = rhs.iter();
                while let Some(&Symbol::Constant(c)) = rhs_iter.next() {
                    // While we read a constant prefix of rhs that does not start with the same constant as lhs, we add it to pref
                    if Some(c) != next {
                        pref.push(c)
                    } else {
                        break;
                    }
                }
                if !pref.is_empty() {
                    let mut pref =
                        StringTerm::constant(pref.into_iter().collect::<String>().as_str());
                    if rhs_iter.next().is_some() {
                        pref = StringTerm::concat(pref, StringTerm::variable(x));
                    }
                    Some((x, Term::String(pref)))
                } else {
                    None
                }
            }
            (Some(_), Some(Symbol::Variable(x))) => {
                let next = match rhs.iter().skip(1).next() {
                    Some(Symbol::Variable(_)) => return subs, // Cannot infer anything
                    Some(Symbol::Constant(c)) => Some(*c),
                    None => None,
                };
                let mut pref = vec![];
                let mut lhs_iter = lhs.iter();
                while let Some(&Symbol::Constant(c)) = lhs_iter.next() {
                    // While we read a constant prefix of rhs that does not start with the same constant as lhs, we add it to pref
                    if Some(c) != next {
                        pref.push(c)
                    } else {
                        break;
                    }
                }

                if !pref.is_empty() {
                    let mut pref =
                        StringTerm::constant(pref.into_iter().collect::<String>().as_str());
                    if lhs_iter.next().is_some() {
                        pref = StringTerm::concat(pref, StringTerm::variable(x));
                    }
                    Some((x, Term::String(pref)))
                } else {
                    None
                }
            }
            _ => None,
        };
        match sub_term {
            Some((x, t)) => subs.set(x, t),
            None => (),
        }
        subs
    }

    fn derive_suffix_sub(eq: &WordEquation) -> Substitution {
        let mut subs = Substitution::new();
        for (x, t) in Self::derive_prefix_sub(&eq.reverse()).iter() {
            if let Term::String(st) = t {
                subs.set(x, Term::String(st.reverse()));
            }
        }
        subs
    }

    fn combine_substitutions(sub1: &Substitution, sub2: &Substitution) -> Option<Substitution> {
        let mut combined = Substitution::new();
        for (x, t1) in sub1.iter() {
            match sub2.get(x) {
                Some(t2) => {
                    if let (Term::String(st1), Term::String(st2)) = (t1, t2) {
                        match (st1, st2) {
                            // Two constants
                            (StringTerm::Constant(c1), StringTerm::Constant(c2)) => {
                                if c1 == c2 {
                                    combined.set(x, t1.clone())
                                } else {
                                    // Conflict
                                    return None;
                                }
                            }
                            // Prefix/Suffix and constant
                            (StringTerm::Constant(c), StringTerm::Concat(p, s))
                            | (StringTerm::Concat(p, s), StringTerm::Constant(c)) => {
                                debug_assert!(p.as_ref() == &StringTerm::variable(x));
                                if let StringTerm::Constant(c2) = s.as_ref() {
                                    if c2 == c {
                                        combined.set(x, StringTerm::Constant(c.clone()).into())
                                    } else {
                                        // Conflict
                                        return None;
                                    }
                                } else {
                                    unreachable!()
                                }
                            }
                            // Prefix and Prefix
                            (StringTerm::Concat(p1, s1), StringTerm::Concat(p2, s2)) => {
                                if let (StringTerm::Constant(c1), StringTerm::Constant(c2)) =
                                    (p1.as_ref(), p2.as_ref())
                                {
                                    // Prefix and prefix
                                    debug_assert!(s1.as_ref() == &StringTerm::variable(x));
                                    debug_assert!(s2.as_ref() == &StringTerm::variable(x));
                                    if c1.starts_with(c2) {
                                        combined.set(
                                            x,
                                            StringTerm::concat(
                                                StringTerm::Constant(c1.clone()),
                                                s1.as_ref().clone(),
                                            )
                                            .into(),
                                        )
                                    } else if c2.starts_with(c1) {
                                        combined.set(
                                            x,
                                            StringTerm::concat(
                                                StringTerm::Constant(c2.clone()),
                                                s1.as_ref().clone(),
                                            )
                                            .into(),
                                        )
                                    } else {
                                        // Conflict
                                        return None;
                                    }
                                } else if let (StringTerm::Constant(c1), StringTerm::Constant(c2)) =
                                    (s1.as_ref(), s2.as_ref())
                                {
                                    // Suffix and suffix
                                    debug_assert!(s1.as_ref() == &StringTerm::variable(x));
                                    debug_assert!(s2.as_ref() == &StringTerm::variable(x));
                                    if c1.ends_with(c2) {
                                        combined.set(
                                            x,
                                            StringTerm::concat(
                                                StringTerm::Constant(c1.clone()),
                                                s1.as_ref().clone(),
                                            )
                                            .into(),
                                        )
                                    } else if c2.ends_with(c1) {
                                        combined.set(
                                            x,
                                            StringTerm::concat(
                                                s1.as_ref().clone(),
                                                StringTerm::Constant(c2.clone()),
                                            )
                                            .into(),
                                        )
                                    } else {
                                        // Conflict
                                        return None;
                                    }
                                } else if let (
                                    StringTerm::Constant(_c1),
                                    StringTerm::Constant(_c2),
                                ) = (p1.as_ref(), s2.as_ref())
                                {
                                    // Prefix and suffix
                                    debug_assert!(s1.as_ref() == &StringTerm::variable(x));
                                    debug_assert!(p2.as_ref() == &StringTerm::variable(x));
                                    //TODO: Implement this case
                                } else if let (
                                    StringTerm::Constant(_c1),
                                    StringTerm::Constant(_c2),
                                ) = (s1.as_ref(), p2.as_ref())
                                {
                                    // Suffix and prefix
                                    debug_assert!(p1.as_ref() == &StringTerm::variable(x));
                                    debug_assert!(s2.as_ref() == &StringTerm::variable(x));
                                    //TODO: Implement this case
                                }
                            }

                            _ => unreachable!("All cases covered"),
                        }
                    }
                }
                None => combined.set(x, t1.clone()),
            }
        }

        for (x, t1) in sub2.iter() {
            if combined.get(x).is_none() {
                combined.set(x, t1.clone());
            }
        }

        Some(combined)
    }
}

/// Checks whether we can obtain suffixes by removing the prefix of the same length from both sides for which Parikk vectors of constants are equal, but the Parikh vectors of variables are not. In that case the equation has no solution.
#[allow(dead_code)]
fn check_parikh(weq: &WordEquation) {
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
            // return false
        }
    }

    // unchanged
}

#[cfg(test)]
mod tests {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::model::{words::Pattern, Sort, VarManager};

    use super::*;

    #[test]
    fn test_strip_const_prefix_no_match() {
        let lhs = Pattern::constant("foo");
        let rhs = Pattern::constant("bar");
        let eq = WordEquation::new(lhs.into(), rhs.into());
        assert_eq!(WordEquationStripPrefixSuffix::strip_matches(&eq), None);
    }

    #[test]
    fn test_strip_const_prefix_match() {
        let lhs = Pattern::constant("foofoo");
        let rhs = Pattern::constant("foobar");
        let eq = WordEquation::new(lhs.into(), rhs.into());
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new(
                Pattern::constant("foo"),
                Pattern::constant("bar")
            ))
        );
    }

    #[test]
    fn test_strip_const_suffix_match() {
        let lhs = Pattern::constant("foobar");
        let rhs = Pattern::constant("barbar");
        let eq = WordEquation::new(lhs.into(), rhs.into());
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new(
                Pattern::constant("foo"),
                Pattern::constant("bar")
            ))
        );
    }

    #[test]
    fn test_strip_const_prefixsuffix_match() {
        let lhs = Pattern::constant("fooabcbar");
        let rhs = Pattern::constant("foodefbar");
        let eq = WordEquation::new(lhs.into(), rhs.into());
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new(
                Pattern::constant("abc"),
                Pattern::constant("def")
            ))
        );
    }

    #[test]
    fn test_strip_prefix_eq() {
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&WordEquation::empty()),
            None
        );
    }

    #[quickcheck]
    fn strip_returns_factor(weq: WordEquation) -> TestResult {
        match WordEquationStripPrefixSuffix::strip_matches(&weq) {
            Some(stripped) => {
                assert!(
                    weq.lhs().contains(stripped.lhs()) && weq.rhs().contains(stripped.rhs()),
                    "stripped: {}\n original: {}",
                    stripped,
                    weq
                );
                TestResult::passed()
            }
            _ => TestResult::discard(),
        }
    }

    #[quickcheck]
    fn strip_suffix_returns_prefix(weq: WordEquation) -> bool {
        match WordEquationStripPrefixSuffix::strip_matches(&weq) {
            Some(stripped) => {
                weq.lhs().starts_with(stripped.lhs()) && weq.rhs().starts_with(stripped.rhs())
            }
            _ => true,
        }
    }

    #[quickcheck]
    fn const_prefixsuffix_match(weq: WordEquation) -> TestResult {
        if weq.lhs().is_empty() || weq.rhs().is_empty() {
            return TestResult::discard();
        }
        match (&weq.lhs().first().unwrap(), &weq.rhs().first().unwrap()) {
            (Symbol::Constant(pa), Symbol::Constant(pb)) => {
                match (&weq.lhs().last().unwrap(), &weq.rhs().last().unwrap()) {
                    (Symbol::Constant(sa), Symbol::Constant(sb)) => {
                        assert_eq!(
                            WordEquationPrefixSuffixMatch::consts_match(&weq),
                            pa == pb && sa == sb
                        );
                        TestResult::passed()
                    }
                    _ => return TestResult::discard(),
                }
            }
            _ => TestResult::discard(),
        }
    }

    #[test]
    fn trivial_empty() {
        assert!(WordEquationTrivial::is_trivial(&WordEquation::empty()) == Some(true))
    }

    #[quickcheck]
    fn trivial_iff_no_var(eq: WordEquation) {
        if eq.lhs().is_constant() && eq.rhs().is_constant() {
            assert!(matches!(WordEquationTrivial::is_trivial(&eq), Some(_)));
        } else {
            assert!(matches!(WordEquationTrivial::is_trivial(&eq), None));
        }
    }

    #[test]
    fn derive_prefix_sub_trivial_eq() {
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x);
        let rhs = Pattern::constant("foo");
        let eq = WordEquation::new(lhs, rhs);

        let mut expected = Substitution::new();
        expected.set(&x, Term::String("foo".into()));

        let got = WordEquationSubstitutions::derive_prefix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_trivial_eq() {
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x);
        let rhs = Pattern::constant("foo");
        let eq = WordEquation::new(lhs.into(), rhs.into());
        let mut expected = Substitution::new();
        expected.set(&x, Term::String("foo".into()));

        let got = WordEquationSubstitutions::derive_suffix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }

    #[test]
    fn derive_prefix_sub_const_none() {
        // Cannot ifer that X starts with 'ab' as it could be empty
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let y = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new(lhs, rhs);

        let expected = Substitution::new();

        let got = WordEquationSubstitutions::derive_prefix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_const_none() {
        // Cannot ifer that Y ends with 'ab' as it could be empty
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let y = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new(lhs, rhs);

        let expected = Substitution::new();

        let got = WordEquationSubstitutions::derive_suffix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }

    #[test]
    fn derive_prefix_sub_const_word() {
        // Infer that x must start with 'foo'
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let y = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("fooab").append_var(&y).clone();
        let eq = WordEquation::new(lhs, rhs);

        let mut expected = Substitution::new();
        expected.set(
            &x,
            StringTerm::concat(StringTerm::constant("foo"), StringTerm::variable(&x)).into(),
        );

        let got = WordEquationSubstitutions::derive_prefix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_const_word() {
        // Infer that y must end with 'foo'
        let mut vm = VarManager::new();
        let x = vm.tmp_var(Sort::String);
        let y = vm.tmp_var(Sort::String);
        let lhs = Pattern::variable(&x).append_word("abfoo").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new(lhs, rhs);

        let mut expected = Substitution::new();
        expected.set(
            &y,
            StringTerm::concat(StringTerm::variable(&y), StringTerm::constant("foo")).into(),
        );

        let got = WordEquationSubstitutions::derive_suffix_sub(&eq);
        assert_eq!(got, expected, "Expected: {} but got {}", expected, got);
    }
}
