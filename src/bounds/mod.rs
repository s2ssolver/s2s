//! Bounds on integer variables and the length of string variables.

pub mod infer;
pub mod step;

use std::{
    cmp::Ordering,
    fmt::Display,
};

use indexmap::IndexMap;
use quickcheck::Arbitrary;

use crate::repr::Variable;

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
        match (self, other) {
            (BoundValue::PosInf, BoundValue::PosInf) => Some(Ordering::Equal),
            (BoundValue::NegInf, BoundValue::NegInf) => Some(Ordering::Equal),
            (BoundValue::PosInf, _) => Some(Ordering::Greater),
            (BoundValue::NegInf, _) => Some(Ordering::Less),
            (_, BoundValue::PosInf) => Some(Ordering::Less),
            (_, BoundValue::NegInf) => Some(Ordering::Greater),
            (BoundValue::Num(n1), BoundValue::Num(n2)) => n1.partial_cmp(n2),
        }
    }
}
impl Ord for BoundValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
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
        BoundValue::Num(value as i32)
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
    fn len(&self) -> Option<usize> {
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
}

impl Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lower, self.upper)
    }
}

/// The bounds of the variables in the formula.
/// Each variable is associated with an interval that represents the possible values the variable can take.
/// For integer variables, this interval represents the domain of the variable.
/// For string variables, this interval represents the length of the string.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Bounds {
    bounds: IndexMap<Variable, Interval>,
}

impl Bounds {
    pub fn empty() -> Self {
        Self::default()
    }

    /// Sets the bound of a variable.
    /// If the variable is not present in the bounds, it is added.
    /// If the variable is already present, the bound is updated.
    ///
    /// # Arguments
    /// - `var` - The variable whose bound is to be set.
    /// - `interval` - The interval that represents the bound of the variable.
    ///
    /// # Returns
    /// The previous bound of the variable, if it was present in the bounds.
    /// Otherwise, returns `None`.
    pub fn set(&mut self, var: Variable, interval: Interval) -> Option<Interval> {
        self.bounds.insert(var, interval)
    }

    /// Returns the bound of a variable.
    /// If the variable is not present in the bounds, returns `None`.
    pub fn get(&self, var: &Variable) -> Option<Interval> {
        self.bounds.get(var).copied()
    }

    /// Returns the upper bound of a variable.
    /// If the variable is not present in the bounds, returns `None`.
    pub fn get_upper(&self, var: &Variable) -> Option<BoundValue> {
        self.get(var).map(|i| i.upper())
    }

    /// Returns the upper bound of the variable as a finite integer.
    /// If the variable is not present in the bounds or the upper bound is not finite, returns `None`.
    pub fn get_upper_finite(&self, var: &Variable) -> Option<i32> {
        self.get_upper(var).and_then(|b| b.as_num())
    }

    /// Returns the lower bound of a variable.
    pub fn get_lower(&self, var: &Variable) -> Option<BoundValue> {
        self.get(var).map(|i| i.lower())
    }

    /// Returns the lower bound of the variable as a finite integer.
    /// If the variable is not present in the bounds or the lower bound is not finite, returns `None`.
    pub fn get_lower_finite(&self, var: &Variable) -> Option<i32> {
        self.get_lower(var).and_then(|b| b.as_num())
    }

    /// Removes the bound of a variable.
    /// If the variable is not present in the bounds, returns `None`.
    /// Otherwise, returns the bound of the variable that was removed.
    pub fn remove(&mut self, var: &Variable) -> Option<Interval> {
        self.bounds.remove(var)
    }

    /// Returns the number of variables in the bounds.
    pub fn len(&self) -> usize {
        self.bounds.len()
    }

    /// Returns true if the bounds are empty and false otherwise.
    /// The bounds are considered empty if there are no variables in the bounds.
    pub fn is_empty(&self) -> bool {
        self.bounds.is_empty()
    }

    /// Intersects two `Bounds` instances and returns a new `Bounds` with the intersection.
    ///
    /// The intersection only includes variables that exist in both `Bounds`.
    /// For each variable, the intersection of the corresponding intervals is computed.
    ///
    /// # Arguments
    ///
    /// * `other` - The other `Bounds` to intersect with.
    ///
    /// # Returns
    ///
    /// A new `Bounds` containing the intersections of the intervals for common variables.
    pub fn intersect(&self, other: &Self) -> Self {
        let mut intersection_map = IndexMap::new();

        for (var, interval) in &self.bounds {
            if let Some(other_interval) = other.get(var) {
                let intersected_interval = interval.intersect(other_interval);
                intersection_map.insert(var.clone(), intersected_interval);
            }
        }

        Self {
            bounds: intersection_map,
        }
    }

    /// Returns an iterator over the variables and their bounds.
    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Interval)> {
        self.bounds.iter()
    }
}

impl Display for Bounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (var, domain) in &self.bounds {
            write!(f, "{}: {}, ", var, domain)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use crate::repr::Sort;

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

    #[test]
    fn test_insert_and_get() {
        let mut interval_map = Bounds::default();

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let interval = Interval::new(1, 5);

        interval_map.set(var.clone(), interval);

        assert_eq!(interval_map.get(&var), Some(Interval::new(1, 5)));
    }

    #[test]
    fn test_remove() {
        let mut interval_map = Bounds::default();

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let interval = Interval::new(1, 5);

        interval_map.set(var.clone(), interval);
        let removed = interval_map.remove(&var);

        assert_eq!(removed, Some(Interval::new(1, 5)));
        assert!(interval_map.get(&var).is_none());
    }

    #[test]
    fn test_len_and_is_empty() {
        let mut interval_map = Bounds::default();

        assert_eq!(interval_map.len(), 0);
        assert!(interval_map.is_empty());

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let interval = Interval::new(1, 5);

        interval_map.set(var, interval);

        assert_eq!(interval_map.len(), 1);
        assert!(!interval_map.is_empty());
    }

    #[test]
    fn test_bounds_intersection() {
        let mut bounds1 = Bounds::default();
        let mut bounds2 = Bounds::default();

        let var_x = Variable::new(0, "x".to_string(), Sort::Int);
        let var_y = Variable::new(1, "y".to_string(), Sort::Int);

        bounds1.set(var_x.clone(), Interval::new(1, 10));
        bounds1.set(var_y.clone(), Interval::new(20, 30));

        bounds2.set(var_x.clone(), Interval::new(5, 15));
        bounds2.set(var_y.clone(), Interval::new(25, 35));

        let intersection = bounds1.intersect(&bounds2);

        assert_eq!(intersection.len(), 2);
        assert_eq!(intersection.get(&var_x), Some(Interval::new(5, 10)));
        assert_eq!(intersection.get(&var_y), Some(Interval::new(25, 30)));
    }

    #[test]
    fn test_bounds_intersection_empty() {
        let mut bounds1 = Bounds::default();
        let mut bounds2 = Bounds::default();

        let var_x = Variable::new(0, "x".to_string(), Sort::Int);

        bounds1.set(var_x.clone(), Interval::new(1, 10));
        bounds2.set(var_x.clone(), Interval::new(15, 20));

        let intersection = bounds1.intersect(&bounds2);

        assert!(
            intersection.get(&var_x).unwrap().is_empty(),
            "Expected empty but got {}",
            intersection
        );
    }

    #[test]
    fn test_bounds_intersection_disjoint_vars() {
        let mut bounds1 = Bounds::default();
        let mut bounds2 = Bounds::default();

        let var_x = Variable::new(0, "x".to_string(), Sort::Int);
        let var_y = Variable::new(1, "y".to_string(), Sort::Int);

        bounds1.set(var_x.clone(), Interval::new(1, 10));
        bounds2.set(var_y.clone(), Interval::new(5, 15));

        let intersection = bounds1.intersect(&bounds2);

        assert!(intersection.is_empty());
    }
}

impl Arbitrary for Interval {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let v1 = isize::arbitrary(g);
        let v2 = isize::arbitrary(g);
        Interval::new(v1.min(v2), v1.max(v2))
    }
}
