//! Functions for increasing bounds on variables.

use crate::node::Sorted;

use super::{BoundValue, Bounds, Interval};

/// A step function that increases a the size of a given [`Interval`].
/// For an interval `[a, b]`, the step function creates a new interval `f([a, b]) = [fl(a), fu(b)]` where `fl` and `fu` are functions such that
/// `fl(a) <= a` and `fu(b) >= b`.
///
/// `BoundStep` provides various methods to increase bounds:
/// - Adding/Subtracting a constant value to the bounds.
/// - Setting the bounds to the next/previous square number.
/// - Doubling the bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BoundStep {
    /// Adds or substracts a a constant offset.
    /// For lower bounds the offset is subtracted, for upper bounds it is added.
    /// That is, if `k` is the offset, then applying this function to a bound [l, u] results in [l-k, u+k].
    ConstantOffset(usize),

    /// Expands the bounds to the next/previous perfect square.
    #[default]
    NextSquare,

    /// Doubles the size of the interval.
    /// This is done by subtracting half of the interval length from the lower bound and adding the same to the upper bound.
    Double,
}

impl BoundStep {
    fn apply_upper(&self, interval: Interval) -> BoundValue {
        match interval.upper() {
            BoundValue::PosInf => BoundValue::PosInf,
            BoundValue::NegInf => BoundValue::NegInf,
            BoundValue::Num(ubound) => match self {
                BoundStep::ConstantOffset(k) => ubound
                    .checked_add(*k as i32)
                    .map(BoundValue::Num)
                    .unwrap_or(BoundValue::PosInf),
                BoundStep::NextSquare => {
                    if ubound >= 0 {
                        // next base is (sqrt(ubound).floor() + 1)
                        let base = (ubound.abs() as f64).sqrt().floor() as i32 + 1;
                        // next perfect square is base^2
                        base.checked_mul(base)
                            .map(BoundValue::Num)
                            .unwrap_or(BoundValue::PosInf)
                    } else {
                        // next  is (sqrt(ubound).ceil() - 1)
                        let base = (ubound.abs() as f64).sqrt().ceil() as i32 - 1;
                        // next perfect square is -base^2
                        base.checked_mul(base)
                            .map(|v| BoundValue::Num(-v))
                            .unwrap_or(BoundValue::PosInf)
                    }
                }
                BoundStep::Double => {
                    if let Some(len) = interval.len() {
                        ubound
                            .checked_add(((len / 2) as i32).max(1))
                            .map(BoundValue::Num)
                            .unwrap_or(BoundValue::PosInf)
                    } else {
                        BoundValue::PosInf
                    }
                }
            },
        }
    }

    fn apply_lower(&self, interval: Interval) -> BoundValue {
        match interval.lower() {
            BoundValue::PosInf => BoundValue::PosInf,
            BoundValue::NegInf => BoundValue::NegInf,
            BoundValue::Num(lbound) => match self {
                BoundStep::ConstantOffset(k) => lbound
                    .checked_sub(*k as i32)
                    .map(BoundValue::Num)
                    .unwrap_or(BoundValue::NegInf),
                BoundStep::NextSquare => {
                    if lbound > 0 {
                        // next base is (sqrt(lbound).ceil() - 1)
                        let base = (lbound.abs() as f64).sqrt().ceil() as i32 - 1;
                        // next smaller perfect square is base^2
                        base.checked_mul(base)
                            .map(BoundValue::Num)
                            .unwrap_or(BoundValue::PosInf)
                    } else {
                        // next is (sqrt(lbound).floor() + 1)
                        let lbound = lbound as f64;
                        let base = lbound.abs().sqrt().floor() as i32 + 1;
                        //let base = (lbound.abs() as f64).sqrt().ceil() as isize + 1;
                        // next smaller perfect square is -base^2
                        base.checked_mul(base)
                            .map(|v| BoundValue::Num(-v))
                            .unwrap_or(BoundValue::PosInf)
                    }
                }
                BoundStep::Double => {
                    if let Some(len) = interval.len() {
                        lbound
                            .checked_sub(((len / 2) as i32).max(1))
                            .map(BoundValue::Num)
                            .unwrap_or(BoundValue::NegInf)
                    } else {
                        BoundValue::NegInf
                    }
                }
            },
        }
    }

    pub fn apply(&self, interval: Interval) -> Interval {
        Interval {
            lower: self.apply_lower(interval),
            upper: self.apply_upper(interval),
        }
    }
}

#[allow(dead_code)]
pub fn update_bounds(bounds: &Bounds, step: BoundStep) -> Bounds {
    let mut new_bounds = Bounds::default();
    for (var, interval) in bounds.iter() {
        if var.sort().is_int() {
            new_bounds.set(var.clone(), step.apply(*interval));
        } else if var.sort().is_string() {
            // Only update the upper bound for string variables
            new_bounds.set(
                var.clone(),
                Interval::new(interval.lower().clone(), step.apply_upper(*interval)),
            );
        } else {
            unreachable!(
                "Variable `{}` has sort {}; it cannot have bounds",
                var,
                var.sort()
            );
        }
    }
    new_bounds
}

#[cfg(test)]
mod tests {

    use quickcheck_macros::quickcheck;

    use super::*;

    #[quickcheck]
    fn constant_offset_valid(interval: Interval, offset: usize) -> bool {
        let offset = (offset % 1000) + 1; // Limit the offset to a reasonable value and make sure it is not 0
        let step = BoundStep::ConstantOffset(offset);
        let new_interval = step.apply(interval);
        new_interval.lower() < interval.lower() && new_interval.upper() > interval.upper()
    }

    #[quickcheck]
    fn next_square_valid(interval: Interval) {
        let step = BoundStep::NextSquare;
        let new_interval = step.apply(interval);
        assert!(
            new_interval.lower() < interval.lower(),
            "Expected: {} < {}",
            interval,
            new_interval
        );
        assert!(new_interval.upper() > interval.upper());
    }

    #[quickcheck]
    fn double_valid(interval: Interval) {
        if interval.len().unwrap_or(0) == 0 {
            return;
        }
        let step = BoundStep::Double;
        let new_interval = step.apply(interval);
        assert!(
            new_interval.lower() < interval.lower(),
            "Expected: {} < {}",
            interval.lower(),
            new_interval.lower()
        );
        assert!(new_interval.upper() > interval.upper());
    }

    #[test]
    fn test_next_square_positive() {
        let interval = Interval::new(10, 20);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(9)); // Strictly less than 10
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(25)); // Strictly greater than 20
    }

    #[test]
    fn test_next_square_negative() {
        let interval = Interval::new(-8, -5);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-9)); // Strictly less than -8
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(-4)); // Strictly greater than 5
    }

    #[test]
    fn test_constant_offset_positive_bounds() {
        let interval = Interval::new(10, 20);
        let step = BoundStep::ConstantOffset(5);
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(5)); // 10 - 5 = 5
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(25)); // 20 + 5 = 25
    }

    #[test]
    fn test_constant_offset_negative_bounds() {
        let interval = Interval::new(-20, -10);
        let step = BoundStep::ConstantOffset(5);
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-25)); // -20 - 5 = -25
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(-5)); // -10 + 5 = -5
    }

    #[test]
    fn test_constant_offset_mixed_bounds() {
        let interval = Interval::new(-10, 10);
        let step = BoundStep::ConstantOffset(3);
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-13)); // -10 - 3 = -13
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(13)); // 10 + 3 = 13
    }

    #[test]
    fn test_constant_offset_zero_bound() {
        let interval = Interval::new(0, 10);
        let step = BoundStep::ConstantOffset(5);
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-5)); // 0 - 5 = -5
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(15)); // 10 + 5 = 15
    }

    #[test]
    fn test_next_square_positive_bound() {
        let interval = Interval::new(2, 15);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(1)); // 1^2 = 1
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(16)); // 4^2 = 16
    }

    #[test]
    fn test_next_square_negative_bound() {
        let interval = Interval::new(-15, -2);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-16)); //
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(-1)); // -
    }

    #[test]
    fn test_next_square_zero_bound() {
        let interval = Interval::new(0, 10);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(-1)); // Next square for 0 is -1
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(16)); // Next square for 10 is 16
    }

    #[test]
    fn test_double_positive_bounds() {
        let interval = Interval::new(10, 20);
        let step = BoundStep::Double;
        let enlarged_interval = step.apply(interval);
        let expected_lower = 10 - ((20 - 10 + 1) / 2); // 10 - 5 = 5
        let expected_upper = 20 + ((20 - 10 + 1) / 2); // 20 + 5 = 25
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(expected_lower));
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(expected_upper));
    }

    #[test]
    fn test_double_negative_bounds() {
        let interval = Interval::new(-20, -10);
        let step = BoundStep::Double;
        let enlarged_interval = step.apply(interval);
        let expected_lower = -20 - ((-10 + 20 + 1) / 2); // -20 - 5 = -25
        let expected_upper = -10 + ((-10 + 20 + 1) / 2); // -10 + 5 = -5
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(expected_lower));
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(expected_upper));
    }

    #[test]
    fn test_double_mixed_bounds() {
        let interval = Interval::new(-5, 5);
        let step = BoundStep::Double;
        let enlarged_interval = step.apply(interval);
        let expected_lower = -5 - ((5 + 5 + 1) / 2); // -5 - 5 = -10
        let expected_upper = 5 + ((5 + 5 + 1) / 2); // 5 + 5 = 10
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(expected_lower));
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(expected_upper));
    }

    #[test]
    fn test_double_zero_bound() {
        let interval = Interval::new(0, 10);
        let step = BoundStep::Double;
        let enlarged_interval = step.apply(interval);
        let expected_lower = 0 - ((10 - 0 + 1) / 2); // 0 - 5 = -5
        let expected_upper = 10 + ((10 - 0 + 1) / 2); // 10 + 5 = 15
        assert_eq!(enlarged_interval.lower(), BoundValue::Num(expected_lower));
        assert_eq!(enlarged_interval.upper(), BoundValue::Num(expected_upper));
    }

    #[test]
    fn test_constant_offset_infinity_bounds() {
        let interval = Interval::new(BoundValue::NegInf, BoundValue::PosInf);
        let step = BoundStep::ConstantOffset(5);
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::NegInf); // Infinity remains unchanged
        assert_eq!(enlarged_interval.upper(), BoundValue::PosInf); // Infinity remains unchanged
    }

    #[test]
    fn test_next_square_infinity_bounds() {
        let interval = Interval::new(BoundValue::NegInf, BoundValue::PosInf);
        let step = BoundStep::NextSquare;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::NegInf); // Infinity remains unchanged
        assert_eq!(enlarged_interval.upper(), BoundValue::PosInf); // Infinity remains unchanged
    }

    #[test]
    fn test_double_infinity_bounds() {
        let interval = Interval::new(BoundValue::NegInf, BoundValue::PosInf);
        let step = BoundStep::Double;
        let enlarged_interval = step.apply(interval);
        assert_eq!(enlarged_interval.lower(), BoundValue::NegInf); // Infinity remains unchanged
        assert_eq!(enlarged_interval.upper(), BoundValue::PosInf); // Infinity remains unchanged
    }
}
