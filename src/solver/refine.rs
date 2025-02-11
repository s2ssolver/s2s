//! Functions for increasing bounds on variables.

use core::panic;
use std::hash::Hash;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    abstraction::LitDefinition,
    interval::{BoundValue, Interval},
    node::{canonical::Literal, get_entailed_literals, Node, NodeKind, NodeManager},
    sat::{Cnf, PLit},
};

use crate::bounds::{BoundInferer, Bounds};
use crate::domain::{Domain, VarDomain};

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
        Interval::new(self.apply_lower(interval), self.apply_upper(interval))
    }
}

pub enum BoundRefinement {
    /// The bounds have been refined.
    Refined(Domain),
    /// The bounds are already equal to or larger than the bounds of the smallest model of the combination of literals.
    /// If there is no satisfying assignment within the current bounds, then the formula is unsatisfiable.
    SmallModelReached,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Cube(IndexSet<Literal>);

impl Hash for Cube {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for l in self.0.iter() {
            l.hash(state);
        }
    }
}

pub(super) struct BoundRefiner {
    _cadical: cadical::Solver,
    _entailed_defs: IndexSet<PLit>,

    conflict_cubes: Vec<Cube>,
    cube_bounds: IndexMap<Cube, Bounds>,
}

impl BoundRefiner {
    pub fn new(skeleton: Cnf) -> Self {
        let mut cadical = cadical::Solver::new();
        for clause in skeleton.into_iter() {
            cadical.add_clause(clause);
        }
        BoundRefiner {
            _cadical: cadical,
            _entailed_defs: IndexSet::new(),
            conflict_cubes: Vec::new(),
            cube_bounds: IndexMap::new(),
        }
    }

    /// Refines the bounds of the string and integer variables in the domain based on the given literals.
    pub fn refine_bounds(
        &mut self,
        literals: &[LitDefinition],
        bounds: &Domain,
        fm: &Node,
        step: BoundStep,
        mngr: &mut NodeManager,
    ) -> BoundRefinement {
        // Find the small-model bounds of any combination of the literal
        let smp_bounds = match self.small_mode_bounds_dnf(literals, fm, mngr) {
            Some(b) => b,
            None => return BoundRefinement::SmallModelReached, // No satisfying assignment
        };

        let mut small_model_reached = true;
        let mut bounds = bounds.clone();

        // Update the bounds of the variables in literals based on the step function but clamp to the small-model bounds
        let vars = literals
            .iter()
            .flat_map(|l| l.defined().variables())
            .collect::<IndexSet<_>>();
        for v in vars {
            // Check if the variable is bounded
            if let Some(current_dom) = bounds.get(&v) {
                match current_dom {
                    VarDomain::Int(current_bounds) | VarDomain::String(current_bounds) => {
                        let increased = step.apply(current_bounds);
                        let clamped =
                            increased.intersect(smp_bounds.get(&v).unwrap_or_else(|| {
                                if current_dom.is_int() {
                                    Interval::unbounded()
                                } else {
                                    Interval::bounded_below(0)
                                }
                            }));
                        // Ensure we don't shrink the upper bounds or increase the lower bounds
                        let new_lower = clamped.lower().min(current_bounds.lower());
                        let new_upper = clamped.upper().max(current_bounds.upper());
                        let new_bounds = Interval::new(new_lower, new_upper);
                        if new_bounds != current_bounds {
                            // changed
                            small_model_reached = false;
                        }
                        // TODO: Check if the limit is reached
                        match current_dom {
                            VarDomain::Int(_) => bounds.set_int(v.clone(), new_bounds),
                            VarDomain::String(_) => bounds.set_string(v.clone(), new_bounds),
                            VarDomain::Bool => unreachable!(),
                        };
                    }
                    VarDomain::Bool => {} // keep as is
                }
            }
        }

        if small_model_reached {
            BoundRefinement::SmallModelReached
        } else {
            BoundRefinement::Refined(bounds)
        }
    }

    /// Legacy implementation of the small-model bounds computation.
    /// This iterates all subsets of the literals and computes the bounds for each subset.
    /// This is way coarser than the dnf based implementation.
    /// Computes the small-model bounds for any combinations given literals that can be satisfied by the formula.
    fn _small_model_bounds(
        &mut self,
        literals: &[LitDefinition],
        fm: &Node,
        mngr: &mut NodeManager,
    ) -> Option<Bounds> {
        // Split literals into entailed and not entailed
        let entailed = get_entailed_literals(fm);
        let (mut entailed, not_entailed): (Vec<_>, Vec<_>) = literals
            .iter()
            .partition(|l| entailed.contains(l.defined()));

        // We check if some more are entailed by invoking the SAT solver.
        let mut new_not_entailed = Vec::new();
        for l in not_entailed.into_iter() {
            if self._entailed_defs.contains(&l.defining()) {
                // This is also entailed
                entailed.push(l);
                log::debug!("Entailed: {}", l);
                continue;
            } else if let Some(false) = self._cadical.solve_with(vec![-l.defining()]) {
                // This is also entailed
                entailed.push(l);
                self._entailed_defs.insert(l.defining());
                log::debug!("Entailed: {}", l);
            } else {
                new_not_entailed.push(l);
            }
        }
        let not_entailed = new_not_entailed;

        let mut base_inferer = BoundInferer::default();
        for l in entailed {
            base_inferer.add_literal(l.defined().clone(), mngr);
        }
        // The bounds of the conjunction of all entailed literals.
        // If these are conflicting, then any combination of literals is conflicting.
        let base_bounds = base_inferer.infer()?;

        // Build all possible combinations of the entailed literals.
        // That it, compute the subset of the power set of the literals such that each subset contains all entailed literals.
        // For each combination compute the small-model bounds.
        let mut combinations: Vec<(BoundInferer, Bounds)> =
            Vec::with_capacity(2usize.pow(not_entailed.len() as u32 + 1));
        combinations.push((base_inferer, base_bounds));

        // Dynamic programming to build the combinations.
        // We filter out any combination that is conflicting.
        for l in not_entailed {
            let mut new_combinations = Vec::new();
            for (inferer, _) in &combinations {
                let mut new_inferer = inferer.clone();
                new_inferer.add_literal(l.defined().clone(), mngr);
                if let Some(bounds) = new_inferer.infer() {
                    new_combinations.push((new_inferer, bounds));
                }
            }
            combinations.extend(new_combinations);
        }
        Self::max_smp_of(combinations.into_iter().map(|(_, b)| b).collect())
    }

    fn max_smp_of(alternatives: Vec<Bounds>) -> Option<Bounds> {
        // There are no combinations with non-conflicting bounds.
        if alternatives.is_empty() {
            None
        } else {
            // For each variable, take the minimum of the lower bounds and the maximum of the upper bounds.
            let mut smp_bounds = Bounds::default();
            for bounds in alternatives {
                for (v, b) in bounds.iter() {
                    match smp_bounds.get(v) {
                        Some(existings) => {
                            let lower = std::cmp::min(existings.lower(), b.lower());
                            let upper = std::cmp::max(existings.upper(), b.upper());
                            smp_bounds.set(v.clone(), Interval::new(lower, upper));
                        }
                        None => {
                            smp_bounds.set(v.clone(), *b);
                        }
                    }
                }
            }
            Some(smp_bounds)
        }
    }

    fn small_mode_bounds_dnf(
        &mut self,
        defs: &[LitDefinition],
        fm: &Node,
        mngr: &mut NodeManager,
    ) -> Option<Bounds> {
        // build the dnf of fm but only with the the given literals
        let present_lits: IndexSet<Literal> =
            IndexSet::from_iter(defs.iter().map(|d| d.defined().clone()));

        let dnf = Self::build_dnf(&present_lits, fm);
        log::info!("DNF has {} cubes", dnf.len());
        log::debug!(
            "DNF: \n{}",
            dnf.iter()
                .map(|c| format!(
                    "{}",
                    c.0.iter()
                        .map(|l| l.to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                ))
                .collect::<Vec<_>>()
                .join("\n")
        );

        let mut alternatives = Vec::new();
        for cube in dnf.into_iter().sorted_by(|a, b| a.0.len().cmp(&b.0.len())) {
            // check if there is a subset of conflicting literals

            if self.conflict_cubes.iter().any(|c| c.0.is_subset(&cube.0)) {
                continue;
            }
            log::debug!("Bounds for cube [{}]:", cube.0.iter().join(","));
            if let Some(b) = self.cube_bounds.get(&cube) {
                alternatives.push(b.clone());
                continue;
            } else {
                let mut inferer = BoundInferer::default();

                for l in &cube.0 {
                    inferer.add_literal(l.clone(), mngr);
                }

                if let Some(bounds) = inferer.infer() {
                    log::debug!("\t{}", bounds);
                    alternatives.push(bounds);
                } else {
                    log::debug!("\tConflicting");
                    self.conflict_cubes.push(cube.clone());
                }
            }
        }
        Self::max_smp_of(alternatives)
    }

    fn build_dnf(literals: &IndexSet<Literal>, fm: &Node) -> Vec<Cube> {
        match fm.kind() {
            NodeKind::And => {
                let mut dnf = vec![Cube(IndexSet::new())];
                for child in fm.children() {
                    let child_dnf = Self::build_dnf(literals, child);
                    // build the cross product
                    let mut new_dnf = Vec::new();
                    for cube in dnf.into_iter() {
                        for ccube in child_dnf.iter() {
                            let mut new_cube = cube.clone();
                            let mut conflict = false;
                            for l in &ccube.0 {
                                if new_cube.0.contains(&l.flip_polarity()) {
                                    // conflicting literals
                                    conflict = true;
                                    break;
                                }
                                new_cube.0.insert(l.clone());
                            }
                            if !conflict {
                                new_dnf.push(new_cube);
                            }
                        }
                    }
                    dnf = new_dnf;
                }
                dnf
            }
            NodeKind::Or => {
                let mut dnf = Vec::new();
                for child in fm.children() {
                    let child_dnf = Self::build_dnf(literals, child);
                    dnf.extend(child_dnf);
                }
                dnf
            }
            NodeKind::Literal(l) => {
                let c = if literals.contains(l) {
                    IndexSet::from_iter(vec![l.clone()])
                } else {
                    IndexSet::new()
                };
                vec![Cube(c)]
            }
            _ => panic!("Unexpected node kind: {:?}", fm.kind()),
        }
    }
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
        let expected_lower = 0 - ((10 + 1) / 2); // 0 - 5 = -5
        let expected_upper = 10 + ((10 + 1) / 2); // 10 + 5 = 15
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
