use std::cmp::{max, min};

use indexmap::{indexset, IndexSet};

use crate::{
    bounds::{infer, Bounds, IntDomain},
    error::Error,
    instance::Instance,
    model::Sort,
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

impl BoundUpdate {
    pub fn unwrap(self) -> Bounds {
        match self {
            BoundUpdate::Next(b) => b,
            BoundUpdate::LimitReached => panic!("Called unwarp on BoundUpdate::LimitReached"),
            BoundUpdate::ThresholdReached => {
                panic!("Called unwarp on BoundUpdate::ThresholdReached")
            }
        }
    }
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
        .chain(b1.iter().map(|(v, _)| v))
        .collect::<Vec<_>>();
    for v in vars {
        let b1 = b1.get(v);
        let b2 = b2.get(v);
        let maxb = b1.join(&b2);

        max.set(v, maxb);
    }
    let def = b1.get_default().join(&b2.get_default());
    max.set_default(def);
    max
}

/// Returns false if the bounds of at least one variable in `current_bounds` are greater than the bounds in `last`.
fn limit_reached(current_bounds: &Bounds, last: &Bounds) -> bool {
    for v in last.iter().map(|(v, _)| v) {
        match (current_bounds.get(v).get_upper(), last.get(v).get_upper()) {
            (Some(c), Some(l)) => {
                if c > l {
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
            Some(b) => bounds.set(v, IntDomain::Bounded(b, b)),
            None => bounds.set(v, IntDomain::Bounded(def_bounds, def_bounds)),
        };
    }
    if let Some(th) = instance.get_upper_threshold() {
        if bounds.uppers_geq(th as isize) {
            return Ok(BoundUpdate::ThresholdReached);
        }
    }

    Ok(BoundUpdate::Next(bounds))
}

pub(super) fn next_bounds(
    mngr: &EncodingManager,
    solver: &cadical::Solver,
    last: &Bounds,
    threshold: Option<usize>,
) -> Result<BoundUpdate, Error> {
    let failed = collect_failed(mngr, solver);
    assert!(failed.len() > 0, "Formula cannot be unsat with empty core");
    let limit_bounds = underapprox(&failed)?;
    log::debug!("Upper Bounds for core: {}", limit_bounds);
    if let Some(th) = threshold {
        if last.uppers_geq(th as isize) {
            return Ok(BoundUpdate::ThresholdReached);
        }
    }

    if limit_bounds.any_empty() {
        return Ok(BoundUpdate::LimitReached);
    }
    if limit_reached(&limit_bounds, last) {
        return Ok(BoundUpdate::LimitReached);
    }
    let mut vars_to_update = indexset! {};
    for c in failed {
        vars_to_update.extend(c.constraint().vars().iter().map(|x| {
            if x.is_string() {
                x.len_var().unwrap()
            } else {
                x.clone()
            }
        }));
    }
    let mut next = last.clone();
    let mut was_updated = false;
    for v in vars_to_update.iter() {
        let mut updated = last.get(v);

        if let Some(u) = updated.get_upper() {
            // next square
            let mut new_upper = ((u as f64).sqrt() + 1f64).powi(2) as isize;
            if let Some(limit) = limit_bounds.get_upper(v) {
                new_upper = min(new_upper, limit);
            }
            if new_upper > u {
                updated.set_upper(new_upper);
                was_updated = true
            }
        } else {
            panic!("No upper bound for variable {} ({})", v, last);
        }
        if let Some(l) = updated.get_lower() {
            let new_lower = max(0, limit_bounds.get_lower(v).unwrap_or(l));
            updated.set_lower(new_lower);
        }
        assert!(next.get(v).get_upper().is_some());
        next.set(v, updated);
    }
    if !was_updated {
        return Ok(BoundUpdate::LimitReached);
    }
    if let Some(th) = threshold {
        next.clamp_uppers(th as isize);
    }

    Ok(BoundUpdate::Next(next))
}

fn underapprox(constraints: &Vec<EncodingContext>) -> Result<Bounds, Error> {
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
    let mut bounds = infer_for(&base)?;

    if bounds.any_empty() {
        log::debug!("Empty bounds on asserted constraints: {:?}", base);
        return Ok(bounds);
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
            let these = infer_for(&new_set)?;

            for s in &new_set {}
            if these.any_empty() {
                continue;
            } else {
                bounds = join(bounds, these);
            }

            // TODO: Filter sets with empty bounds
            new_sets.push(new_set);
        }
        powerset.extend(new_sets);
    }

    Ok(bounds)
}
