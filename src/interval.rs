//! Bounds on integer variables and the length of string variables.

use std::{cmp::Ordering, fmt::Display};

use quickcheck::Arbitrary;

/// Represents a value that can either be a finite integer, positive infinity,
/// or negative infinity.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum BoundValue {
    PosInf,
    NegInf,
    Num(i32),
}

impl PartialOrd for BoundValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BoundValue {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (BoundValue::PosInf, BoundValue::PosInf) => Ordering::Equal,
            (BoundValue::NegInf, BoundValue::NegInf) => Ordering::Equal,
            (BoundValue::PosInf, _) => Ordering::Greater,
            (BoundValue::NegInf, _) => Ordering::Less,
            (_, BoundValue::PosInf) => Ordering::Less,
            (_, BoundValue::NegInf) => Ordering::Greater,
            (BoundValue::Num(n1), BoundValue::Num(n2)) => n1.cmp(n2),
        }
    }
}

impl std::ops::Mul for BoundValue {
    type Output = BoundValue;

    /// Multiplies two `BoundValue`s.
    /// The following rules are used:
    /// - `Num(n1) * Num(n2) = Num(n1 * n2)`
    /// - `X * Num(0) = Num(0)` and `Num(0) * X = Num(0)` for any `X`
    /// - `PosInf * Num(n) = PosInf` if `n > 0`
    /// - `PosInf * Num(n) = NegInf` if `n < 0`
    /// - `NegInf * Num(n) = PosInf` if `n < 0`
    /// - `NegInf * Num(n) = NegInf` if `n > 0`
    /// - `PosInf * PosInf = PosInf`
    /// - `NegInf * NegInf = PosInf`
    /// - `PosInf * NegInf = NegInf` and  `NegInf * PosInf = NegInf`
    fn mul(self, other: BoundValue) -> BoundValue {
        match (self, other) {
            (BoundValue::Num(n1), BoundValue::Num(n2)) => match n1.checked_mul(n2) {
                Some(v) => BoundValue::Num(v),
                None => {
                    if n1.signum() == n2.signum() {
                        BoundValue::PosInf
                    } else {
                        BoundValue::NegInf
                    }
                }
            },
            (_, BoundValue::Num(0)) | (BoundValue::Num(0), _) => BoundValue::Num(0),
            (BoundValue::PosInf, BoundValue::Num(n)) | (BoundValue::Num(n), BoundValue::PosInf) => {
                if n > 0 {
                    BoundValue::PosInf
                } else if n < 0 {
                    BoundValue::NegInf
                } else {
                    BoundValue::Num(0)
                }
            }
            (BoundValue::NegInf, BoundValue::Num(n)) | (BoundValue::Num(n), BoundValue::NegInf) => {
                if n < 0 {
                    BoundValue::PosInf
                } else if n > 0 {
                    BoundValue::NegInf
                } else {
                    BoundValue::Num(0)
                }
            }
            (BoundValue::PosInf, BoundValue::PosInf) | (BoundValue::NegInf, BoundValue::NegInf) => {
                BoundValue::PosInf
            }
            (BoundValue::PosInf, BoundValue::NegInf) | (BoundValue::NegInf, BoundValue::PosInf) => {
                BoundValue::NegInf
            }
        }
    }
}

impl BoundValue {
    /// Returns `Some(n=` if the value is a finite integer `n` and `None` otherwise.
    pub fn as_num(&self) -> Option<i32> {
        match self {
            BoundValue::Num(n) => Some(*n),
            _ => None,
        }
    }
}

impl From<i32> for BoundValue {
    fn from(value: i32) -> Self {
        BoundValue::Num(value)
    }
}

impl From<u32> for BoundValue {
    fn from(value: u32) -> Self {
        BoundValue::Num(value as i32)
    }
}

// Similarly, implement for other types if needed
impl From<i64> for BoundValue {
    fn from(value: i64) -> Self {
        BoundValue::Num(value as i32)
    }
}

impl From<u64> for BoundValue {
    fn from(value: u64) -> Self {
        BoundValue::Num(value as i32)
    }
}

// Implement for usize, u8, i8, etc.
impl From<isize> for BoundValue {
    fn from(value: isize) -> Self {
        BoundValue::Num(value as i32)
    }
}

impl From<usize> for BoundValue {
    fn from(value: usize) -> Self {
        BoundValue::Num(value as i32)
    }
}

impl Display for BoundValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundValue::PosInf => write!(f, "∞"),
            BoundValue::NegInf => write!(f, "-∞"),
            BoundValue::Num(n) => write!(f, "{}", n),
        }
    }
}

/// Represents an interval [l, u] where the bounds `l` and `u`
/// can be either finite integers, positive infinity, or negative infinity.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Interval {
    /// The lower bound of the interval.
    lower: BoundValue,
    /// The upper bound of the interval.
    upper: BoundValue,
}

impl Interval {
    /// Creates a new interval with the specified lower and upper bounds.
    ///
    /// # Arguments
    ///
    /// * `lower` - The lower bound of the interval.
    /// * `upper` - The upper bound of the interval.
    ///
    /// # Returns
    ///
    /// A new `Interval` with the specified bounds.
    pub fn new(lower: impl Into<BoundValue>, upper: impl Into<BoundValue>) -> Self {
        Self {
            lower: lower.into(),
            upper: upper.into(),
        }
    }

    /// Creates an interval that is bounded above and unbounded below.
    ///
    /// # Arguments
    ///
    /// * `upper` - The upper bound of the interval.
    ///
    /// # Returns
    ///
    /// A new `Interval` with the specified upper bound and negative infinity as the lower bound.
    pub fn bounded_above(upper: impl Into<BoundValue>) -> Self {
        Self::new(BoundValue::NegInf, upper)
    }

    /// Creates an interval that is bounded below and unbounded above.
    ///
    /// # Arguments
    ///
    /// * `lower` - The lower bound of the interval.
    ///
    /// # Returns
    ///
    /// A new `Interval` with the specified lower bound and positive infinity as the upper bound.
    pub fn bounded_below(lower: impl Into<BoundValue>) -> Self {
        Self::new(lower, BoundValue::PosInf)
    }

    /// Creates an unbounded interval.
    ///
    /// # Returns
    ///
    /// A new `Interval` that spans from negative infinity to positive infinity.
    pub fn unbounded() -> Self {
        Self::new(BoundValue::NegInf, BoundValue::PosInf)
    }

    /// Checks if the interval is empty.
    ///
    /// An interval is considered empty if its lower bound is greater than its upper bound.
    pub fn is_empty(&self) -> bool {
        self.lower > self.upper
    }

    /// Returns the upper bound of the interval.
    pub fn upper(&self) -> BoundValue {
        self.upper
    }

    /// Returns the upper bound of the interval as a finite integer if it is finite and `None` otherwise.
    pub fn upper_finite(&self) -> Option<i32> {
        self.upper.as_num()
    }

    /// Returns the lower bound of the interval as a finite integer if it is finite and `None` otherwise.
    pub fn lower_finite(&self) -> Option<i32> {
        self.lower.as_num()
    }

    /// Returns the lower bound of the interval.
    pub fn lower(&self) -> BoundValue {
        self.lower
    }

    /// Intersects two intervals and returns the resulting interval.
    /// The intersection of two intervals is the interval that contains all values that are in both intervals.
    ///
    /// # Returns
    /// A new `Interval` representing the intersection of the two intervals.
    /// If the intersection is empty, the resulting interval will have `lower > upper`.
    pub fn intersect(&self, other: Self) -> Self {
        let lower = self.lower.max(other.lower);
        let upper = self.upper.min(other.upper);

        Self::new(lower, upper)
    }

    /// Returns the length of the interval.
    /// The length of the interval is the cardinality of the set of values in the interval.
    /// If the interval is empty, the length is 0.
    /// If the interval is unbounded, the length is infinite, in which case `None` is returned.
    pub fn len(&self) -> Option<usize> {
        match (self.lower, self.upper) {
            (BoundValue::Num(l), BoundValue::Num(u)) => {
                if l > u {
                    Some(0)
                } else {
                    Some((u as isize - l as isize + 1) as usize)
                }
            }
            (BoundValue::NegInf, BoundValue::Num(_)) => None,
            (BoundValue::Num(_), BoundValue::PosInf) => None,
            (BoundValue::NegInf, BoundValue::PosInf) => None,
            _ => Some(0),
        }
    }

    pub fn with_upper(&self, upper: BoundValue) -> Self {
        Self::new(self.lower, upper)
    }

    pub fn with_lower(&self, lower: BoundValue) -> Self {
        Self::new(lower, self.upper)
    }
}

impl Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lower, self.upper)
    }
}

impl Arbitrary for Interval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let v1 = isize::arbitrary(g);
        let v2 = isize::arbitrary(g);
        Interval::new(v1.min(v2), v1.max(v2))
    }
}

#[cfg(test)]
mod tests {

    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn test_interval_new() {
        let interval = Interval::new(3, 10);
        assert_eq!(interval.lower(), BoundValue::Num(3));
        assert_eq!(interval.upper(), BoundValue::Num(10));
    }

    #[test]
    fn test_bounded_above() {
        let interval = Interval::bounded_above(10);
        assert_eq!(interval.lower(), BoundValue::NegInf);
        assert_eq!(interval.upper(), BoundValue::Num(10));
    }

    #[test]
    fn test_bounded_below() {
        let interval = Interval::bounded_below(3);
        assert_eq!(interval.lower(), BoundValue::Num(3));
        assert_eq!(interval.upper(), BoundValue::PosInf);
    }

    #[test]
    fn test_unbounded() {
        let interval = Interval::unbounded();
        assert_eq!(interval.lower(), BoundValue::NegInf);
        assert_eq!(interval.upper(), BoundValue::PosInf);
    }

    #[test]
    fn test_is_empty() {
        let interval = Interval::new(10, 5);
        assert!(interval.is_empty());

        let non_empty_interval = Interval::new(5, 10);
        assert!(!non_empty_interval.is_empty());
    }

    #[test]
    fn test_partial_cmp() {
        assert!(BoundValue::PosInf > BoundValue::Num(100));
        assert!(BoundValue::NegInf < BoundValue::Num(-100));
        assert_eq!(
            BoundValue::Num(50).partial_cmp(&BoundValue::Num(50)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            BoundValue::Num(10).partial_cmp(&BoundValue::Num(20)),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn test_intersect_overlapping_intervals() {
        let interval1 = Interval::new(3, 10);
        let interval2 = Interval::new(5, 12);
        let result = interval1.intersect(interval2);
        assert_eq!(result, Interval::new(5, 10));
    }

    #[test]
    fn test_intersect_non_overlapping_intervals() {
        let interval1 = Interval::new(3, 5);
        let interval2 = Interval::new(6, 10);
        let result = interval1.intersect(interval2);
        assert!(result.is_empty(),);
    }

    #[test]
    fn test_intersect_touching_intervals() {
        let interval1 = Interval::new(3, 5);
        let interval2 = Interval::new(5, 10);
        let result = interval1.intersect(interval2);
        assert_eq!(result, Interval::new(5, 5));
    }

    #[test]
    fn test_intersect_with_infinite_bounds() {
        let interval1 = Interval::new(BoundValue::NegInf, 10);
        let interval2 = Interval::new(5, BoundValue::PosInf);
        let result = interval1.intersect(interval2);
        assert_eq!(result, Interval::new(5, 10));
    }

    #[quickcheck]
    fn test_with_upper(i: Interval, u: usize) {
        let with_upper = i.with_upper(u.into());
        assert_eq!(with_upper.lower(), i.lower());
        assert_eq!(with_upper.upper(), u.into());
    }

    #[quickcheck]
    fn test_with_lower(i: Interval, l: usize) {
        let with_lower = i.with_lower(l.into());
        assert_eq!(with_lower.lower(), l.into());
        assert_eq!(with_lower.upper(), i.upper());
    }
}
