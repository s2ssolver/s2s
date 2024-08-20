use std::{
    cmp::{max, min},
    collections::HashSet,
};

use indexmap::{indexset, IndexSet};

use crate::{
    ast::Sort,
    bounds::{infer, Bounds, IntDomain},
    error::ErrorRepr as Error,
    instance::Instance,
    sat::Cnf,
};

use super::manager::{EncodingContext, EncodingManager};

/// The result of increasing the bounds used for solving.
pub(super) enum BoundUpdate {
    /// The next bounds to be used
    Next(Bounds),
    /// The current bounds are sufficient, if the instance is satisfiable
    LimitReached,
    /// User-imposed threshold reached, cannot increase bounds further
    ThresholdReached,
}

pub(super) fn collect_failed(
    mngr: &EncodingManager,
    solver: &cadical::Solver,
) -> Vec<EncodingContext> {
    let mut failed = Vec::new();

    assert!(solver.status() == Some(false));
    for (ctx, _) in mngr.iter() {
        let watchers = mngr.get_watching_literals(ctx);
        for w in watchers {
            if solver.failed(w) {
                failed.push(ctx.clone());
                break;
            }
        }
    }
    failed
}

fn infer_for(on: &IndexSet<&EncodingContext>) -> Result<Bounds, Error> {
    infer(
        &on.iter()
            .cloned()
            .map(|ctx| ctx.constraint())
            .cloned()
            .collect::<Vec<_>>(),
    )
}

fn join(b1: Bounds, b2: Bounds) -> Bounds {
    let mut max = Bounds::new();
    let vars = b1
        .iter()
        .map(|(v, _)| v)
        .chain(b2.iter().map(|(v, _)| v))
        .collect::<Vec<_>>();

    for v in vars {
        let b1 = b1.get(v);
        let b2 = b2.get(v);
        match (b1, b2) {
            (None, None) => (), // Keep default
            (None, Some(a)) | (Some(a), None) => {
                // Keep the one set
                max.set(v, a.clone());
            }
            (Some(b1), Some(b2)) => {
                // Join the bounds of both
                let maxb = b1.join(&b2);
                max.set(v, maxb);
            }
        }
    }
    let def = b1.get_default().join(&b2.get_default());
    max.set_default(def);
    max
}

/// Returns false if the bounds of at least one variable in `current_bounds` are greater than the bounds in `last`.
fn limit_reached(limit: &Bounds, other: &Bounds) -> bool {
    for v in other.iter().map(|(v, _)| v) {
        match (
            limit.get_with_default(v).get_upper(),
            other.get_with_default(v).get_upper(),
        ) {
            (Some(ul), Some(u)) => {
                if ul > u {
                    return false;
                }
            }
            (Some(_), None) => (),
            (None, _) => return false, // Unbounded
        }
        match (
            limit.get_with_default(v).get_lower(),
            other.get_with_default(v).get_lower(),
        ) {
            (Some(ul), Some(l)) => {
                if ul < l {
                    return false;
                }
            }
            (Some(_), None) => (),
            (None, _) => return false, // Unbounded
        }
    }

    true
}

pub(super) fn init_bounds(
    mngr: &EncodingManager,
    instance: &Instance,
) -> Result<BoundUpdate, Error> {
    // Use the set containing all asserted literals as the base case
    let base: IndexSet<&EncodingContext> = mngr
        .iter()
        .map(|(ctx, _)| ctx)
        .filter(|ctx| ctx.is_asserted())
        .collect();
    for c in base.iter() {
        log::debug!("Asserted: {}", c.constraint());
    }
    let base_bounds = infer_for(&base)?;
    if base_bounds.any_empty() {
        log::debug!("Empty bounds on asserted constraints: {}", base_bounds);
        return Ok(BoundUpdate::LimitReached);
    }
    // Use the lower bounds as the upper bounds for the first round.
    // If a variable is unbounded, use the instance's lower bound instead
    let mut bounds = Bounds::new();
    let def_bounds = instance.get_start_bound() as isize;
    for v in instance.vars_of_sort(Sort::Int) {
        match base_bounds.get_lower(v) {
            Some(b) => bounds.set(v, IntDomain::Bounded(b, max(b, def_bounds))),
            None => bounds.set(v, IntDomain::Bounded(0, def_bounds)),
        };
    }
    if let Some(th) = instance.get_upper_threshold() {
        bounds.clamp(-(th as isize), th as isize);
    }

    Ok(BoundUpdate::Next(bounds))
}

fn get_limit_bound(
    failed: &Vec<EncodingContext>,
    skeleton: Option<&Cnf>,
) -> Result<BoundUpdate, Error> {
    for c in failed.iter() {
        log::debug!("Failed: {}", c.constraint());
    }
    assert!(
        !failed.is_empty(),
        "Formula cannot be unsat with empty core"
    );
    let limit_bounds = if failed.len() <= 10 {
        match underapprox(&failed, skeleton)? {
            Some(bounds) => bounds,
            None => return Ok(BoundUpdate::LimitReached),
        }
    } else {
        // Unbounded for all variables
        Bounds::new()
    };
    Ok(BoundUpdate::Next(limit_bounds))
}
pub(super) fn next_bounds(
    mngr: &EncodingManager,
    solver: &cadical::Solver,
    last: &Bounds,
    instance: &Instance,
    skeleton: Option<&Cnf>,
) -> Result<BoundUpdate, Error> {
    // TODO: Check here if Threshold was reached

    let failed = collect_failed(mngr, solver);
    let limit_bounds = match get_limit_bound(&failed, skeleton)? {
        BoundUpdate::Next(b) => b,
        BoundUpdate::LimitReached => return Ok(BoundUpdate::LimitReached),
        BoundUpdate::ThresholdReached => return Ok(BoundUpdate::ThresholdReached),
    };

    log::debug!("Upper Bounds for core: {}", limit_bounds);
    if let Some(th) = instance.get_upper_threshold() {
        if last.uppers_geq(th as isize) {
            return Ok(BoundUpdate::ThresholdReached);
        }
    }
    if limit_bounds.any_empty() || limit_reached(&limit_bounds, last) {
        return Ok(BoundUpdate::LimitReached);
    }

    // Collect the variables that need to be updated
    let mut vars_to_update = indexset! {};
    for c in failed {
        vars_to_update.extend(c.constraint().vars().iter().filter_map(|x| {
            if x.is_string() {
                x.len_var()
            } else if x.is_int() {
                Some(x.clone())
            } else {
                None
            }
        }));
    }
    if vars_to_update.is_empty() {
        // No length-dependent constraints in the core, conclude that the instance is unsatisfiable
        return Ok(BoundUpdate::LimitReached);
    }

    let mut th_reached = true;
    let mut next = last.clone();
    let mut was_updated = false;
    let avg_upper = vars_to_update
        .iter()
        .map(|v| last.get_upper(v).unwrap())
        .sum::<isize>()
        / vars_to_update.len() as isize;
    let avg_lower = vars_to_update
        .iter()
        .map(|v| last.get_lower(v).unwrap())
        .sum::<isize>()
        / vars_to_update.len() as isize;

    for v in vars_to_update.iter() {
        let mut updated = last.get(v).unwrap().clone();
        let last_upper = last.get_upper(v).unwrap();
        let last_lower = last.get_lower(v).unwrap();

        // Clamp to threshold
        if let Some(th) = instance.get_upper_threshold() {
            if last_upper >= th as isize {
                continue;
            }
        }
        th_reached = false;
        // next square
        let mut new_upper = if last_upper <= avg_upper * 2 {
            ((last_upper as f64).sqrt() + 1f64).powi(2) as isize
        } else {
            // If the upper bound is already above the average, increase by 1. This is to avoid growing the bounds too quickly.
            last_upper + 1
        };
        if let Some(limit) = limit_bounds.get_upper(v) {
            new_upper = min(new_upper, limit);
        }
        if let Some(lower) = limit_bounds.get_lower(v) {
            new_upper = max(new_upper, lower);
        }
        if let Some(th) = instance.get_upper_threshold() {
            new_upper = min(new_upper, th as isize);
        }

        if new_upper > last_upper {
            updated.set_upper(new_upper);
            was_updated = true
        }

        if v.is_len_var() {
            let new_lower = max(0, limit_bounds.get_lower(v).unwrap_or(last_lower));
            updated.set_lower(new_lower);
        } else {
            let mut new_lower: isize = if last_lower >= 2 * avg_lower {
                ((last_lower.abs() as f64).sqrt() + 1f64).powi(2) as isize
            } else {
                // If the lower bound is already below the average, decrease by 1. This is to avoid growing the bounds too quickly.
                last_lower - 1
            };
            if last_lower <= 0 {
                new_lower *= -1;
            }
            // Clamp to threshold
            if let Some(th) = instance.get_upper_threshold() {
                if last_lower <= -(th as isize) as isize {
                    continue;
                }
            }

            if let Some(lower) = limit_bounds.get_lower(v) {
                new_lower = max(new_lower, lower);
            }
            if let Some(th) = instance.get_upper_threshold() {
                new_lower = max(new_lower, th as isize);
            }

            if new_lower < last_lower {
                updated.set_lower(new_lower);
                was_updated = true
            }
        }

        assert!(next.get(v).and_then(|b| b.get_upper()).is_some());
        assert!(next.get(v).and_then(|b| b.get_lower()).is_some());
        next.set(v, updated);
    }

    if !was_updated {
        if th_reached {
            return Ok(BoundUpdate::ThresholdReached);
        } else {
            return Ok(BoundUpdate::LimitReached);
        }
    }

    Ok(BoundUpdate::Next(next))
}

fn check_feasible(skeleton: Option<&Cnf>, cs: &IndexSet<&EncodingContext>) -> bool {
    let mut assmpts = HashSet::new();
    for ctx in cs {
        let def = ctx.definitional();
        if assmpts.contains(&(-def)) {
            return false;
        } else {
            assmpts.insert(def);
        }
    }
    // Check if the skeleton is satisfiable when the constraints are asserted
    if let Some(skel) = skeleton {
        let mut cadical: cadical::Solver = cadical::Solver::new();
        for clause in skel.iter() {
            cadical.add_clause(clause.clone());
        }

        match cadical.solve_with(assmpts.into_iter()) {
            Some(false) => return false,
            Some(true) | None => return true,
        }
    }

    true
}

fn underapprox(
    constraints: &Vec<EncodingContext>,
    skeleton: Option<&Cnf>,
) -> Result<Option<Bounds>, Error> {
    // Build powerset of the constraints, which is an underapproximation of the DNF.
    // If a constraint is asserted, move it to all subsets insteads, i.e., remove all subsets that do not contain all asserted constraints.

    let mut powerset = Vec::new();
    // Use the set containing all asserted literals as the base case
    let base: IndexSet<&EncodingContext> =
        constraints.iter().filter(|ctx| ctx.is_asserted()).collect();
    log::info!(
        "Refining bounds for {} failed constraints ({} asserted)",
        constraints.len(),
        base.len()
    );
    for c in constraints {
        if c.is_asserted() {
            log::debug!("Asserted: {}", c.constraint());
        } else {
            log::debug!("Unasserted: {}", c.constraint());
        }
    }
    if !check_feasible(skeleton, &base) {
        return Ok(None);
    }
    let mut bounds = infer_for(&base)?;

    if bounds.any_empty() {
        log::debug!("Empty bounds on asserted constraints: {:?}", base);
        return Ok(Some(bounds));
    }

    powerset.push(base);
    let unasserted = constraints
        .iter()
        .filter(|ctx| !ctx.is_asserted())
        .collect::<IndexSet<&EncodingContext>>();

    // TODO: Check if the bounds of the conjunction of the asserted constraints are empty. If so, return here.

    // For each unasserted constraint, add it to all sets currently in the powerset

    for ctx in unasserted {
        let mut new_sets = Vec::new();
        for set in powerset.iter() {
            let mut new_set = set.clone();
            new_set.insert(ctx);
            if check_feasible(skeleton, &new_set) {
                let these = infer_for(&new_set)?;

                if these.any_empty() {
                    continue;
                } else {
                    bounds = join(bounds, these);
                }

                // TODO: Filter sets with empty bounds
                new_sets.push(new_set);
            } else {
                log::error!("INFEASIBLE: {:?}", new_set);
            }
        }
        powerset.extend(new_sets);
    }

    Ok(Some(bounds))
}
