//! Bounds on integer variables and the length of string variables.

use std::{
    cmp::{max, min},
    fmt::Display,
};

use indexmap::IndexMap;
use quickcheck::Arbitrary;

use crate::model::Variable;

mod infer;

pub use infer::infer;

/// The domain of an integer variable.
/// The domain is represented as a range of possible values.
/// The domain can be bounded by only a lower bound, only an upper bound, an upper and lower bound, or be unbounded (i.e. the variable can take any value).
/// Moreover, the domain can be empty, which means that the variable cannot take any value.
/// All bounds are inclusive, i.e. a variable with domain [a, b] can take the values a, a+1, ..., b.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntDomain {
    /// Is bounded by an upper and lower bound (inclusive).
    /// The lower bound must be less than or equal to the upper bound.
    /// Use `IntDomain::bounded` to create a new bounded domain instead of constructing it directly.
    Bounded(isize, isize),
    ///  Is bounded by a lower bound (inclusive), but unbounded from above
    LowerBounded(isize),
    /// Is bounded by an upper bound (inclusive), but unbounded from below
    UpperBounded(isize),
    /// Is unbounded, the variable can take any value
    Unbounded,
    /// Is empty, the variable cannot take a value
    Empty,
}

impl IntDomain {
    /// Creates a new integer domain that is bounded by the given lower and upper bound.
    fn bounded(lower: isize, upper: isize) -> Self {
        if lower > upper {
            IntDomain::Empty
        } else {
            IntDomain::Bounded(lower, upper)
        }
    }

    /// Returns the upper bound of the domain if it is bounded from above and `None` otherwise.
    pub fn get_upper(&self) -> Option<isize> {
        match self {
            IntDomain::Bounded(_, u) => Some(*u),
            IntDomain::LowerBounded(_) => None,
            IntDomain::UpperBounded(u) => Some(*u),
            IntDomain::Unbounded => None,
            IntDomain::Empty => None,
        }
    }

    /// Returns the upper bound of the domain if it is bounded from above and `None` otherwise.
    pub fn get_lower(&self) -> Option<isize> {
        match self {
            IntDomain::Bounded(l, _) => Some(*l),
            IntDomain::LowerBounded(l) => Some(*l),
            IntDomain::UpperBounded(_) => None,
            IntDomain::Unbounded => None,
            IntDomain::Empty => None,
        }
    }

    /// Sets the upper bound of the domain.
    /// If the domain is bounded from above, updates the upper bound.
    /// If the domain is not bounded from above, imposes an upper bound.
    /// If the domain is empty, does nothing.
    pub fn set_upper(&mut self, upper: isize) {
        match self {
            IntDomain::UpperBounded(u) | IntDomain::Bounded(_, u) => *u = upper,
            IntDomain::LowerBounded(l) => *self = Self::bounded(*l, upper),
            IntDomain::Unbounded => *self = Self::UpperBounded(upper),
            IntDomain::Empty => {}
        }
    }

    /// Sets the lower bound of the domain.
    /// If the domain is bounded from below, updates the lower bound.
    /// If the domain is not bounded from below, imposes a lower bound.
    /// If the domain is empty, does nothing.
    pub fn set_lower(&mut self, lower: isize) {
        match self {
            IntDomain::LowerBounded(l) | IntDomain::Bounded(l, _) => *l = lower,
            IntDomain::UpperBounded(u) => *self = Self::bounded(lower, *u),
            IntDomain::Unbounded => *self = Self::LowerBounded(lower),
            IntDomain::Empty => {}
        }
    }

    /// Intersects two integer domains.
    /// The intersection of two bounded domains is the intersection of the two ranges.
    /// That is, if the first domain is [a, b] and the second domain is [c, d], then the intersection is [max(a, c), min(b, d)].
    /// If one domain is bounded and the other is unbounded, the intersection is the bounded domain.
    /// If one domain is empty, the intersection is empty.
    fn intersect(&self, other: &Self) -> Self {
        match (self, other) {
            (IntDomain::Empty, _) | (_, IntDomain::Empty) => IntDomain::Empty,
            (IntDomain::Bounded(l1, u1), IntDomain::Bounded(l2, u2)) => {
                Self::bounded(max(*l1, *l2), min(*u1, *u2))
            }

            (IntDomain::LowerBounded(l2), IntDomain::Bounded(l1, u1))
            | (IntDomain::Bounded(l1, u1), IntDomain::LowerBounded(l2)) => {
                Self::bounded(max(*l1, *l2), *u1)
            }

            (IntDomain::UpperBounded(u2), IntDomain::Bounded(l1, u1))
            | (IntDomain::Bounded(l1, u1), IntDomain::UpperBounded(u2)) => {
                Self::bounded(*l1, min(*u1, *u2))
            }

            (IntDomain::Unbounded, IntDomain::Bounded(l1, u1))
            | (IntDomain::Bounded(l1, u1), IntDomain::Unbounded) => Self::bounded(*l1, *u1),

            (IntDomain::LowerBounded(l1), IntDomain::LowerBounded(l2)) => {
                Self::LowerBounded(max(*l1, *l2))
            }

            (IntDomain::UpperBounded(u), IntDomain::LowerBounded(l))
            | (IntDomain::LowerBounded(l), IntDomain::UpperBounded(u)) => Self::bounded(*l, *u),

            (IntDomain::Unbounded, IntDomain::LowerBounded(l))
            | (IntDomain::LowerBounded(l), IntDomain::Unbounded) => Self::LowerBounded(*l),

            (IntDomain::UpperBounded(u1), IntDomain::UpperBounded(u2)) => {
                Self::UpperBounded(min(*u1, *u2))
            }
            (IntDomain::Unbounded, IntDomain::UpperBounded(u))
            | (IntDomain::UpperBounded(u), IntDomain::Unbounded) => Self::UpperBounded(*u),

            (IntDomain::Unbounded, IntDomain::Unbounded) => IntDomain::Unbounded,
        }
    }

    /// Joins two integer domains.
    /// The join of two bounded domains is the smallest bounded domain that contains both domains.
    pub fn join(&self, other: &Self) -> Self {
        match (&self, &other) {
            (IntDomain::Empty, other) | (other, IntDomain::Empty) => *other.clone(),
            (IntDomain::Bounded(l1, u1), IntDomain::Bounded(l2, u2)) => {
                let l = *l1.max(l2);
                let u = *u1.min(u2);
                if l > u {
                    IntDomain::Empty
                } else {
                    IntDomain::Bounded(l, u)
                }
            }
            (IntDomain::Bounded(l1, u2), IntDomain::LowerBounded(l2))
            | (IntDomain::LowerBounded(l2), IntDomain::Bounded(l1, u2)) => {
                let l = *l1.max(l2);
                let u = *u2;
                if l > u {
                    IntDomain::Empty
                } else {
                    IntDomain::Bounded(l, u)
                }
            }
            (IntDomain::Bounded(l1, u1), IntDomain::UpperBounded(u2))
            | (IntDomain::UpperBounded(u2), IntDomain::Bounded(l1, u1)) => {
                let l = *l1;
                let u = *u1.min(u2);
                if l > u {
                    IntDomain::Empty
                } else {
                    IntDomain::Bounded(l, u)
                }
            }
            (_, IntDomain::Unbounded) | (IntDomain::Unbounded, _) => IntDomain::Unbounded,

            (IntDomain::LowerBounded(l1), IntDomain::LowerBounded(l2)) => {
                let l = *l1.max(l2);
                IntDomain::LowerBounded(l)
            }
            (IntDomain::LowerBounded(l), _) | (_, IntDomain::LowerBounded(l)) => {
                IntDomain::LowerBounded(*l)
            }

            (IntDomain::UpperBounded(u), IntDomain::UpperBounded(u2)) => {
                let u = *u.min(u2);
                IntDomain::UpperBounded(u)
            }
        }
    }
}

/// Represents and manages the bounds of integer variables.
/// Every integer variable is associated with a [IntDomain] that represents the possible values the variable can take.
/// This includes length of string variables, which are implicitly viewed as integer variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bounds {
    domains: IndexMap<Variable, IntDomain>,
    default: IntDomain,
}

impl Bounds {
    /// Creates a new bounds object with no bounds set.
    /// By default, all integer variables are unbounded.
    pub fn new() -> Self {
        Self {
            domains: IndexMap::new(),
            default: IntDomain::Unbounded,
        }
    }

    /// Creates a new bounds object with no bounds set.
    /// By default, all integer variables are bounded by the given [IntDomain].
    #[allow(dead_code)]
    pub fn with_defaults(default: IntDomain) -> Self {
        Self {
            domains: IndexMap::new(),
            default,
        }
    }

    pub fn set_default(&mut self, default: IntDomain) {
        self.default = default;
    }
    /// Sets the domain of a variable.
    pub fn set(&mut self, var: &Variable, domain: IntDomain) -> Option<IntDomain> {
        assert!(
            var.is_int(),
            "Cannot add bounds for non-integer variable {}.",
            var
        );
        self.domains.insert(var.clone(), domain)
    }

    /// Gets the domain of a variable.
    pub fn get(&self, var: &Variable) -> IntDomain {
        debug_assert!(
            var.is_int(),
            "Cannot get bounds for non-integer variable {}.",
            var
        );
        match self.domains.get(var) {
            Some(d) => *d,
            None => {
                if var.is_len_var() {
                    let mut df = self.get_default().clone();
                    // Set lower bound to 0 for length variables by default
                    df.set_lower(0);
                    df
                } else {
                    self.default
                }
            }
        }
    }

    /// Returns the upper bound of a variable.
    /// Returns `None` if the variable is unbounded.
    pub fn get_upper(&self, var: &Variable) -> Option<isize> {
        self.get(var).get_upper()
    }

    /// Sets the upper bound of a variable, see [IntDomain::set_upper].
    pub fn set_upper(&mut self, var: &Variable, upper: isize) {
        let mut domain = self.get(var);
        domain.set_upper(upper);
        self.set(var, domain);
    }

    /// Returns the lower bound of a variable, if it is bounded from below.
    /// Returns `None` if the variable is unbounded.
    pub fn get_lower(&self, var: &Variable) -> Option<isize> {
        self.get(var).get_lower()
    }

    pub fn set_lower(&mut self, var: &Variable, lower: isize) {
        let mut domain = self.get(var);
        domain.set_lower(lower);
        self.set(var, domain);
    }

    /// Intesects all domains with the domains in the bounds, see [IntDomain::intersect].
    /// The default domain is also intersected.
    /// Returns the results.
    pub fn intersect(&self, other: &Self) -> Self {
        let mut result = Self::new();
        let decls = self.domains.keys().chain(other.domains.keys());
        for var in decls {
            result.set(var, self.get(var).intersect(&other.get(var)));
        }

        result.default = self.default.intersect(&other.default);

        result
    }

    /// Returns true if all upper bounds are less than or equal to the given value and false otherwise.
    #[allow(dead_code)]
    pub fn uppers_leq(&self, val: isize) -> bool {
        self.domains
            .values()
            .all(|d| d.get_upper().map_or(false, |u| u <= val))
            && self.default.get_upper().map_or(false, |u| u <= val)
    }

    /// Returns true if all upper bounds are greater than or  equal to the given value and false otherwise.
    #[allow(dead_code)]
    pub fn uppers_geq(&self, val: isize) -> bool {
        self.domains
            .values()
            .all(|d| d.get_upper().map_or(true, |u| u >= val))
            && self.default.get_upper().map_or(true, |u| u >= val)
    }

    /// Returns true if the domain of any variable is empty and false otherwise.
    pub fn any_empty(&self) -> bool {
        self.domains.values().any(|d| d == &IntDomain::Empty)
    }

    /// Updates the upper bounds of the variables by calling the given function on each bound, including the default bound.
    /// If a variable is unbounded, it is not updated.
    pub fn update_uppers(&mut self, updater: impl Fn(isize) -> isize) -> bool {
        let mut any_changed = false;
        for dom in self.domains.iter_mut().map(|b| b.1) {
            if let Some(upper) = dom.get_upper() {
                let new_upper = updater(upper);

                if new_upper != upper {
                    dom.set_upper(new_upper);
                    any_changed = true;
                }
            }
        }
        if let Some(def_upper) = self.default.get_upper() {
            let new_default = updater(def_upper);
            if new_default != def_upper {
                self.default.set_upper(new_default);
                any_changed = true;
            }
        }
        any_changed
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &IntDomain)> {
        self.domains.iter()
    }

    pub fn get_default(&self) -> IntDomain {
        self.default
    }

    /// Clamps the upper bounds of all variables to the given limit.
    /// Returns true if any bound was changed and false otherwise.
    pub fn clamp_uppers(&mut self, limit: isize) -> bool {
        self.update_uppers(|b| min(b, limit))
    }

    /// Doubles the bounds of all variables, including the default bound.
    /// The optional clamp can be used to limit the maximum value of the bounds.
    /// Returns true if any bound was changed and false otherwise.
    #[allow(dead_code)]
    pub fn double_uppers(&mut self) -> bool {
        self.update_uppers(|b| b * 2)
    }

    /// Updates the bounds of all variables such that they are the next square number greater than the current value.
    pub fn next_square_uppers(&mut self) -> bool {
        self.update_uppers(|b| ((b as f64).sqrt() + 1f64).powi(2) as isize)
    }
}

/* Pretty Printing */

impl Display for IntDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntDomain::Bounded(l, u) => match l.cmp(u) {
                std::cmp::Ordering::Less => write!(f, "[{}, {}]", l, u),
                std::cmp::Ordering::Equal => write!(f, "{}", l),
                std::cmp::Ordering::Greater => write!(f, "∅"),
            },
            IntDomain::LowerBounded(l) => write!(f, "[{}, ∞)", l),
            IntDomain::UpperBounded(u) => write!(f, "(-∞, {}]", u),
            IntDomain::Unbounded => write!(f, "(-∞, ∞)"),
            IntDomain::Empty => write!(f, "∅"),
        }
    }
}

impl Display for Bounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (var, domain) in &self.domains {
            write!(f, "{}: {}, ", var, domain)?;
        }
        write!(f, "}}")
    }
}

/* Arbitrary */

impl Arbitrary for IntDomain {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let mut l = isize::arbitrary(g);
        let mut u = isize::arbitrary(g);
        while l > u {
            l = isize::arbitrary(g);
            u = isize::arbitrary(g);
        }
        let choices = [
            IntDomain::bounded(l, u),
            IntDomain::LowerBounded(l),
            IntDomain::UpperBounded(u),
            IntDomain::Unbounded,
            IntDomain::Empty,
        ];
        *g.choose(&choices).unwrap()
    }
}

#[cfg(test)]
mod tests {

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::model::Sort;

    use super::*;

    #[test]
    fn int_domain_get_upper() {
        assert_eq!(IntDomain::Bounded(0, 10).get_upper(), Some(10));
        assert_eq!(IntDomain::LowerBounded(0).get_upper(), None);
        assert_eq!(IntDomain::UpperBounded(10).get_upper(), Some(10));
        assert_eq!(IntDomain::Unbounded.get_upper(), None);
        assert_eq!(IntDomain::Empty.get_upper(), None);
    }

    #[test]
    fn int_domain_get_lower() {
        assert_eq!(IntDomain::Bounded(0, 10).get_lower(), Some(0));
        assert_eq!(IntDomain::LowerBounded(0).get_lower(), Some(0));
        assert_eq!(IntDomain::UpperBounded(10).get_lower(), None);
        assert_eq!(IntDomain::Unbounded.get_lower(), None);
        assert_eq!(IntDomain::Empty.get_lower(), None);
    }

    #[test]
    fn int_domain_set_upper() {
        let mut domain = IntDomain::Bounded(0, 10);
        domain.set_upper(5);
        assert_eq!(domain, IntDomain::Bounded(0, 5));

        let mut domain = IntDomain::LowerBounded(0);
        domain.set_upper(5);
        assert_eq!(domain, IntDomain::Bounded(0, 5));

        let mut domain = IntDomain::UpperBounded(10);
        domain.set_upper(5);
        assert_eq!(domain, IntDomain::UpperBounded(5));

        let mut domain = IntDomain::Unbounded;
        domain.set_upper(5);
        assert_eq!(domain, IntDomain::UpperBounded(5));

        let mut domain = IntDomain::Empty;
        domain.set_upper(5);
        assert_eq!(domain, IntDomain::Empty);
    }

    #[test]
    fn int_domain_intersect_empty() {
        assert_eq!(
            IntDomain::Bounded(0, 10).intersect(&IntDomain::Empty),
            IntDomain::Empty
        );
        assert_eq!(
            IntDomain::LowerBounded(0).intersect(&IntDomain::Empty),
            IntDomain::Empty
        );
        assert_eq!(
            IntDomain::UpperBounded(10).intersect(&IntDomain::Empty),
            IntDomain::Empty
        );
        assert_eq!(
            IntDomain::Unbounded.intersect(&IntDomain::Empty),
            IntDomain::Empty
        );
        assert_eq!(
            IntDomain::Empty.intersect(&IntDomain::Empty),
            IntDomain::Empty
        );
    }

    #[test]
    fn int_domain_intersect_lower_bounded() {
        assert_eq!(
            IntDomain::Bounded(0, 10).intersect(&IntDomain::LowerBounded(5)),
            IntDomain::Bounded(5, 10)
        );
        assert_eq!(
            IntDomain::LowerBounded(0).intersect(&IntDomain::LowerBounded(5)),
            IntDomain::LowerBounded(5)
        );
        assert_eq!(
            IntDomain::UpperBounded(10).intersect(&IntDomain::LowerBounded(5)),
            IntDomain::Bounded(5, 10)
        );
        assert_eq!(
            IntDomain::Unbounded.intersect(&IntDomain::LowerBounded(5)),
            IntDomain::LowerBounded(5)
        );
        assert_eq!(
            IntDomain::Empty.intersect(&IntDomain::LowerBounded(5)),
            IntDomain::Empty
        );
    }

    #[quickcheck]
    fn int_domain_intersection_unbounded_neutral(bound: IntDomain) {
        assert_eq!(bound.intersect(&IntDomain::Unbounded), bound);
    }

    #[quickcheck]
    fn int_domain_intersection_empty_is_empty(bound: IntDomain) {
        assert_eq!(bound.intersect(&IntDomain::Empty), IntDomain::Empty);
    }

    #[quickcheck]
    fn int_domain_intersection_lower_greater_upper_is_empty(
        dom1: IntDomain,
        dom2: IntDomain,
    ) -> TestResult {
        if let (Some(l1), Some(u2)) = (dom1.get_lower(), dom2.get_upper()) {
            if l1 > u2 {
                assert_eq!(dom1.intersect(&dom2), IntDomain::Empty);
                return TestResult::passed();
            } else {
                return TestResult::discard();
            }
        }
        TestResult::discard()
    }

    #[quickcheck]
    fn int_domain_intersection_commutes(dom1: IntDomain, dom2: IntDomain) {
        assert_eq!(dom1.intersect(&dom2), dom2.intersect(&dom1));
    }

    #[quickcheck]
    fn int_domain_intersection_correct_lower(dom1: IntDomain, dom2: IntDomain) -> TestResult {
        let inter = dom1.intersect(&dom2);

        if let IntDomain::Empty = inter {
            return TestResult::discard();
        }

        match (dom1.get_lower(), dom2.get_lower()) {
            (Some(l1), Some(l2)) => {
                assert!(inter.get_lower().map_or(false, |l| l >= l1 && l >= l2))
            }
            (None, Some(l1)) | (Some(l1), None) => {
                assert!(inter.get_lower().map_or(false, |l| l >= l1))
            }
            (None, None) => assert!(inter.get_lower().is_none()),
        }
        TestResult::passed()
    }

    #[quickcheck]
    fn int_domain_intersection_correct_upper(dom1: IntDomain, dom2: IntDomain) -> TestResult {
        let inter = dom1.intersect(&dom2);

        if let IntDomain::Empty = inter {
            return TestResult::discard();
        }

        match (dom1.get_upper(), dom2.get_upper()) {
            (Some(u1), Some(u2)) => {
                assert!(inter.get_upper().map_or(false, |u| u <= u1 && u <= u2))
            }
            (None, Some(u1)) | (Some(u1), None) => {
                assert!(inter.get_upper().map_or(false, |u| u <= u1))
            }
            (None, None) => assert!(inter.get_upper().is_none()),
        }
        TestResult::passed()
    }

    #[quickcheck]
    fn bounds_with_default(default: IntDomain) {
        let mut bounds = Bounds::with_defaults(default);
        bounds.default = default;
    }

    #[test]
    fn bounds_default_unbounded() {
        let mut bounds = Bounds::new();
        bounds.default = IntDomain::Unbounded;
    }

    #[quickcheck]
    fn bounds_set_get(domain: IntDomain) {
        let var = Variable::temp(Sort::Int);
        let mut bounds = Bounds::new();
        bounds.set(&var, domain);
        assert_eq!(bounds.get(&var), domain);
    }

    #[test]
    #[should_panic]
    fn bounds_set_non_int() {
        let var = Variable::temp(Sort::String);
        let mut bounds = Bounds::new();
        bounds.set(&var, IntDomain::bounded(5, 10));
    }

    #[test]
    fn bounds_get_lower() {
        let var = Variable::temp(Sort::Int);
        let mut bounds = Bounds::new();
        assert_eq!(bounds.get_lower(&var), None);
        bounds.set(&var, IntDomain::bounded(5, 10));
        assert_eq!(bounds.get_lower(&var), Some(5));
    }

    #[test]
    #[ignore = "Test not implemented"]
    fn bounds_infer_word_eq() {
        let _bounds = Bounds::new();
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented"]
    fn bounds_infer_lincon() {
        let _bounds = Bounds::new();
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented"]
    fn lincon_eq_upper_bounds() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented"]
    fn lincon_geq_upper_bounds() {
        todo!()
    }

    #[test]
    #[ignore = "Test not implemented"]
    fn lincon_leq_upper_bounds() {
        todo!()
    }
}
