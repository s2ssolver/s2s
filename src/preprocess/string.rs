//! Contains preprocessing rules for string constraints.

use std::{cmp::min, fmt::Display};

use indexmap::IndexMap;

use crate::model::{
    constraints::{Pattern, Symbol, WordEquation},
    formula::{Formula, Predicate},
    terms::{StringTerm, Term},
    Substitution, Variable,
};

use super::{PreprocessingResult, Preprocessor};
#[derive(Debug, Default)]
pub struct WordEquationStripPrefixSuffix {}

#[derive(Debug, Default)]
pub struct WordEquationConstMatching {}

#[derive(Debug, Default)]
pub struct WordEquationParikhMatch {}

#[derive(Debug, Default)]
pub struct WordEquationFactorization {}

#[derive(Debug, Default)]
pub struct WordEquationTrivial {}

/// Derives valid substitutions from word equations.
/// If applied, the resulting formula is equisatisfiable to the original one.
/// If the formula is asserted, i.e., always true, the found substitutions are valid for the whole formula.
#[derive(Debug, Default)]
pub struct WordEquationSubstitutions {
    suffixes: IndexMap<Variable, Vec<char>>,
    prefixes: IndexMap<Variable, Vec<char>>,
    eqs: IndexMap<Variable, Vec<char>>,

    conflict: bool,
}

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
            None
        } else {
            let lhs = lhs.factor(i, lhs.len() - j).unwrap_or(Pattern::empty());
            let rhs = rhs.factor(i, rhs.len() - j).unwrap_or(Pattern::empty());
            Some(WordEquation::new(lhs, rhs, eq.eq_type()))
        }
    }
}

impl Preprocessor for WordEquationStripPrefixSuffix {
    fn get_substitution(&self) -> Option<Substitution> {
        None
    }

    fn get_name(&self) -> String {
        String::from("Word Equation Stripping")
    }

    fn apply_predicate(&mut self, predicate: Predicate, _is_asserted: bool) -> PreprocessingResult {
        match predicate {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                let lhs = Pattern::from(lhs);
                let rhs = Pattern::from(rhs);
                let eq = WordEquation::new_equality(lhs, rhs);
                match Self::strip_matches(&eq) {
                    Some(stripped) => {
                        PreprocessingResult::Changed(Formula::predicate(stripped.into()))
                    }
                    None => PreprocessingResult::Unchanged(Formula::predicate(eq.into())),
                }
            }
            _ => PreprocessingResult::Unchanged(Formula::predicate(predicate)),
        }
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }
}

impl WordEquationConstMatching {
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

impl Preprocessor for WordEquationConstMatching {
    fn apply_predicate(&mut self, predicate: Predicate, _is_asserted: bool) -> PreprocessingResult {
        match predicate {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                let lhs = Pattern::from(lhs);
                let rhs = Pattern::from(rhs);
                let eq = WordEquation::new_equality(lhs, rhs);
                if !Self::consts_match(&eq) {
                    PreprocessingResult::Unchanged(Formula::ffalse())
                } else {
                    PreprocessingResult::Unchanged(Formula::predicate(eq.into()))
                }
            }
            _ => PreprocessingResult::Unchanged(Formula::predicate(predicate)),
        }
    }

    fn apply_boolvar(
        &mut self,
        var: crate::model::Variable,
        _is_asserted: bool,
    ) -> PreprocessingResult {
        PreprocessingResult::Unchanged(Formula::boolvar(var))
    }

    fn get_substitution(&self) -> Option<Substitution> {
        None
    }

    fn get_name(&self) -> String {
        String::from("Word Equation Const Matching")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
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
                None
            }
        } else if weq.rhs().is_empty() {
            if weq.lhs().contains_constant() {
                Some(false)
            } else {
                None
            }
        } else if weq.lhs().is_constant() && weq.rhs().is_constant() {
            Some(weq.lhs() == weq.rhs())
        } else {
            None
        }
    }
}

impl Preprocessor for WordEquationTrivial {
    fn apply_predicate(&mut self, predicate: Predicate, _is_asserted: bool) -> PreprocessingResult {
        match predicate {
            Predicate::Equality(Term::String(lhs), Term::String(rhs)) => {
                let lhs = Pattern::from(lhs);
                let rhs = Pattern::from(rhs);
                let eq: WordEquation = WordEquation::new_equality(lhs, rhs);
                match Self::is_trivial(&eq) {
                    Some(true) => PreprocessingResult::Changed(Formula::ttrue()),
                    Some(false) => PreprocessingResult::Changed(Formula::ffalse()),
                    None => PreprocessingResult::Unchanged(Formula::predicate(eq.into())),
                }
            }
            _ => PreprocessingResult::Unchanged(Formula::predicate(predicate)),
        }
    }

    fn get_substitution(&self) -> Option<Substitution> {
        None
    }

    fn get_name(&self) -> String {
        String::from("Word Equation Trivial Reducer")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {}
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum VarConstraint {
    /// The variable must have the given constant prefix
    ConstPrefix(Variable, Vec<char>),
    /// The variable must have the given constant suffix
    ConstSuffix(Variable, Vec<char>),
    /// The variable must be equal to the given constant
    Eq(Variable, Vec<char>),
}

impl VarConstraint {
    fn equal(var: &Variable, val: &str) -> Self {
        VarConstraint::Eq(var.clone(), val.chars().collect())
    }

    fn suffix(var: &Variable, val: &str) -> Self {
        VarConstraint::ConstSuffix(var.clone(), val.chars().collect())
    }

    fn prefix(var: &Variable, val: &str) -> Self {
        VarConstraint::ConstPrefix(var.clone(), val.chars().collect())
    }
}

impl WordEquationSubstitutions {
    /// Derives constant prefix constraints from the given word equation.
    fn derive_const_prefix(eq: &WordEquation) -> Option<VarConstraint> {
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        match (lhs.first(), rhs.first()) {
            (Some(Symbol::Variable(x)), None) | (None, Some(Symbol::Variable(x))) => {
                // x = ""
                Some(VarConstraint::Eq(x.clone(), vec![]))
            }
            (Some(Symbol::Variable(x)), Some(_)) => {
                let next = match lhs.iter().nth(1) {
                    Some(Symbol::Variable(_)) => return None, // Cannot infer anything
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
                let pref_len = pref.len();
                if !pref.is_empty() {
                    if rhs.len() > pref_len {
                        Some(VarConstraint::ConstPrefix(x.clone(), pref))
                    } else {
                        Some(VarConstraint::Eq(x.clone(), pref))
                    }
                } else {
                    None
                }
            }
            (Some(_), Some(Symbol::Variable(x))) => {
                let next = match rhs.iter().nth(1) {
                    Some(Symbol::Variable(_)) => return None, // Cannot infer anything
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
                let pref_len = pref.len();
                if !pref.is_empty() {
                    if lhs.len() > pref_len {
                        Some(VarConstraint::ConstPrefix(x.clone(), pref))
                    } else {
                        Some(VarConstraint::Eq(x.clone(), pref))
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn derive_const_suffix(eq: &WordEquation) -> Option<VarConstraint> {
        match Self::derive_const_prefix(&eq.reverse())? {
            VarConstraint::ConstPrefix(x, p) => {
                Some(VarConstraint::ConstSuffix(x, p.into_iter().rev().collect()))
            }
            VarConstraint::ConstSuffix(_, _) => unreachable!(),
            VarConstraint::Eq(x, e) => Some(VarConstraint::Eq(x, e.into_iter().rev().collect())),
        }
    }

    /// Return false on conflict
    fn add_constraint(&mut self, con: &VarConstraint) {
        if self.conflict {
            return;
        }
        match con {
            VarConstraint::ConstPrefix(x, p) => {
                if let Some(eq) = self.eqs.get(x) {
                    if !eq.starts_with(p) {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::equal(x, String::from_iter(eq).as_str())
                        );
                        self.conflict = true;
                        return;
                    }
                }
                if let Some(prev) = self.prefixes.get(x) {
                    if prev.starts_with(p) {
                        return;
                    } else if p.starts_with(prev) {
                        self.prefixes.insert(x.clone(), p.clone());
                        return;
                    } else {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::prefix(x, String::from_iter(prev).as_str())
                        );
                        self.conflict = true;
                        return;
                    }
                }
                self.prefixes.insert(x.clone(), p.clone());
            }
            VarConstraint::ConstSuffix(x, s) => {
                if let Some(eq) = self.eqs.get(x) {
                    if !eq.ends_with(s) {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::equal(x, String::from_iter(eq).as_str())
                        );
                        self.conflict = true;
                        return;
                    }
                }
                if let Some(suff) = self.suffixes.get(x) {
                    if suff.ends_with(s) {
                        return;
                    } else if s.ends_with(suff) {
                        self.suffixes.insert(x.clone(), s.clone());
                        return;
                    } else {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::suffix(x, String::from_iter(suff).as_str())
                        );
                        self.conflict = true;
                        return;
                    }
                }
                self.suffixes.insert(x.clone(), s.clone());
            }
            VarConstraint::Eq(x, eq) => {
                if let Some(eq2) = self.eqs.get(x) {
                    if eq != eq2 {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::suffix(x, String::from_iter(eq2).as_str())
                        );
                        self.conflict = true;
                        return;
                    }
                }
                if let Some(pref) = self.prefixes.get(x) {
                    if !eq.starts_with(pref) {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::prefix(x, String::from_iter(pref).as_str())
                        );
                        self.conflict = true;
                    } else {
                        self.prefixes.remove(x);
                    }
                }
                if let Some(suff) = self.suffixes.get(x) {
                    if !eq.ends_with(suff) {
                        log::trace!(
                            "Conflict {} and {}",
                            con,
                            VarConstraint::suffix(x, String::from_iter(suff).as_str())
                        );
                        self.conflict = true;
                    } else {
                        self.suffixes.remove(x);
                    }
                }
                self.eqs.insert(x.clone(), eq.clone());
            }
        }
    }
}

impl Preprocessor for WordEquationSubstitutions {
    fn apply_predicate(&mut self, predicate: Predicate, is_asserted: bool) -> PreprocessingResult {
        if !is_asserted {
            return PreprocessingResult::Unchanged(Formula::predicate(predicate));
        }
        if !self.conflict {
            if let Predicate::Equality(Term::String(lhs), Term::String(rhs)) = predicate.clone() {
                let lhs = Pattern::from(lhs);
                let rhs = Pattern::from(rhs);
                let eq: WordEquation = WordEquation::new_equality(lhs, rhs);
                if let Some(pc) = Self::derive_const_prefix(&eq) {
                    log::trace!("From {}: Inferred {}", eq, pc);
                    self.add_constraint(&pc)
                }
                if let Some(sc) = Self::derive_const_suffix(&eq) {
                    log::trace!("From {}: Inferred {}", eq, sc);
                    self.add_constraint(&sc)
                }
            }
        }
        PreprocessingResult::Unchanged(Formula::predicate(predicate))
    }

    fn get_substitution(&self) -> Option<Substitution> {
        if self.conflict {
            None
        } else {
            let mut sub = Substitution::new();
            for (x, p) in &self.prefixes {
                sub.set(
                    x,
                    StringTerm::concat(
                        StringTerm::constant(String::from_iter(p.iter()).as_str()),
                        StringTerm::variable(x),
                    )
                    .into(),
                );
            }
            for (x, s) in &self.suffixes {
                sub.set(
                    x,
                    StringTerm::concat(
                        StringTerm::variable(x),
                        StringTerm::constant(String::from_iter(s.iter()).as_str()),
                    )
                    .into(),
                );
            }
            for (x, e) in &self.eqs {
                sub.set(
                    x,
                    StringTerm::constant(String::from_iter(e.iter()).as_str()).into(),
                );
            }

            Some(sub)
        }
    }

    fn finalize(&mut self, result: PreprocessingResult) -> PreprocessingResult {
        if self.conflict {
            PreprocessingResult::Changed(Formula::ffalse())
        } else {
            result
        }
    }

    fn get_name(&self) -> String {
        String::from("Word Equation Infer Substitutions")
    }

    fn new() -> Self
    where
        Self: Sized,
    {
        Self {
            suffixes: IndexMap::new(),
            prefixes: IndexMap::new(),
            eqs: IndexMap::new(),
            conflict: false,
        }
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

impl Display for VarConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VarConstraint::ConstPrefix(x, p) => {
                write!(f, "{} starts with {}", x, p.iter().collect::<String>())
            }
            VarConstraint::ConstSuffix(x, s) => {
                write!(f, "{} ends with {}", x, s.iter().collect::<String>())
            }
            VarConstraint::Eq(x, e) => write!(f, "{} = {}", x, e.iter().collect::<String>()),
        }
    }
}

#[cfg(test)]
mod tests {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::model::Sort;

    use super::*;

    #[test]
    fn test_strip_const_prefix_no_match() {
        let lhs = Pattern::constant("foo");
        let rhs = Pattern::constant("bar");
        let eq = WordEquation::new_equality(lhs, rhs);
        assert_eq!(WordEquationStripPrefixSuffix::strip_matches(&eq), None);
    }

    #[test]
    fn test_strip_const_prefix_match() {
        let lhs = Pattern::constant("foofoo");
        let rhs = Pattern::constant("foobar");
        let eq = WordEquation::new_equality(lhs, rhs);
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new_equality(
                Pattern::constant("foo"),
                Pattern::constant("bar")
            ))
        );
    }

    #[test]
    fn test_strip_const_suffix_match() {
        let lhs = Pattern::constant("foobar");
        let rhs = Pattern::constant("barbar");
        let eq = WordEquation::new_equality(lhs, rhs);
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new_equality(
                Pattern::constant("foo"),
                Pattern::constant("bar")
            ))
        );
    }

    #[test]
    fn test_strip_const_prefixsuffix_match() {
        let lhs = Pattern::constant("fooabcbar");
        let rhs = Pattern::constant("foodefbar");
        let eq = WordEquation::new_equality(lhs, rhs);
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&eq),
            Some(WordEquation::new_equality(
                Pattern::constant("abc"),
                Pattern::constant("def")
            ))
        );
    }

    #[test]
    fn test_strip_prefix_eq() {
        assert_eq!(
            WordEquationStripPrefixSuffix::strip_matches(&WordEquation::empty_equation()),
            None
        );
    }

    #[quickcheck]
    fn strip_returns_factor(weq: WordEquation) -> TestResult {
        match WordEquationStripPrefixSuffix::strip_matches(&weq) {
            Some(stripped) => {
                assert!(
                    weq.lhs().contains(&stripped.lhs()) && weq.rhs().contains(&stripped.rhs()),
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
    fn const_prefixsuffix_match(weq: WordEquation) -> TestResult {
        if weq.lhs().is_empty() || weq.rhs().is_empty() {
            return TestResult::discard();
        }
        match (&weq.lhs().first().unwrap(), &weq.rhs().first().unwrap()) {
            (Symbol::Constant(pa), Symbol::Constant(pb)) => {
                match (&weq.lhs().last().unwrap(), &weq.rhs().last().unwrap()) {
                    (Symbol::Constant(sa), Symbol::Constant(sb)) => {
                        assert_eq!(
                            WordEquationConstMatching::consts_match(&weq),
                            pa == pb && sa == sb
                        );
                        TestResult::passed()
                    }
                    _ => TestResult::discard(),
                }
            }
            _ => TestResult::discard(),
        }
    }

    #[test]
    fn trivial_empty() {
        assert!(WordEquationTrivial::is_trivial(&WordEquation::empty_equation()) == Some(true))
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
        let x = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x);
        let rhs = Pattern::constant("foo");
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = Some(VarConstraint::equal(&x, "foo"));

        let got = WordEquationSubstitutions::derive_const_prefix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_trivial_eq() {
        let x = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x);
        let rhs = Pattern::constant("foo");
        let eq = WordEquation::new_equality(lhs, rhs);
        let expected = Some(VarConstraint::equal(&x, "foo"));

        let got = WordEquationSubstitutions::derive_const_suffix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }

    #[test]
    fn derive_prefix_sub_const_none() {
        // Cannot ifer that X starts with 'ab' as it could be empty

        let x = Variable::temp(Sort::String);
        let y = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = None;

        let got = WordEquationSubstitutions::derive_const_prefix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_const_none() {
        // Cannot ifer that Y ends with 'ab' as it could be empty

        let x = Variable::temp(Sort::String);
        let y = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = None;

        let got = WordEquationSubstitutions::derive_const_suffix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }

    #[test]
    fn derive_prefix_sub_const_word() {
        // Infer that x must start with 'foo'

        let x = Variable::temp(Sort::String);
        let y = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x).append_word("ab").clone();
        let rhs = Pattern::constant("fooab").append_var(&y).clone();
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = Some(VarConstraint::ConstPrefix(x, "foo".chars().collect()));

        let got = WordEquationSubstitutions::derive_const_prefix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }

    #[test]
    fn derive_suffix_sub_const_word() {
        // Infer that y must end with 'foo'

        let x = Variable::temp(Sort::String);
        let y = Variable::temp(Sort::String);
        let lhs = Pattern::variable(&x).append_word("abfoo").clone();
        let rhs = Pattern::constant("ab").append_var(&y).clone();
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = Some(VarConstraint::ConstSuffix(y, "foo".chars().collect()));

        let got = WordEquationSubstitutions::derive_const_suffix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }
    #[test]
    fn derive_prefix_none() {
        //aaX = XY:

        let x = Variable::temp(Sort::String);
        let y = Variable::temp(Sort::String);
        let lhs = Pattern::constant("aa").append_var(&x).clone();
        let rhs = Pattern::variable(&x).append_var(&y).clone();
        let eq = WordEquation::new_equality(lhs, rhs);

        let expected = None;

        let got = WordEquationSubstitutions::derive_const_prefix(&eq);
        assert_eq!(got, expected, "Expected: {:?} but got {:?}", expected, got);
    }
}
