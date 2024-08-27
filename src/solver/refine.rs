use indexmap::IndexSet;

use crate::{
    bounds::{infer::BoundInferer, step::BoundStep, Bounds, Interval},
    context::Context,
    repr::ir::{Formula, Literal},
};

pub enum BoundRefinement {
    /// The bounds have been refined.
    Refined(Bounds),
    /// The bounds are already equal to or larger than the bounds of the smallest model of the combination of literals.
    /// If there is no satisfying assignment within the current bounds, then the formula is unsatisfiable.
    SmallModelReached,
    /// The (user-defined) limit of bounds has been reached for every variable.
    LimitReached,
}

pub(super) fn refine_bounds(
    literals: &[Literal],
    bounds: &Bounds,
    fm: &Formula,
    step: BoundStep,
    ctx: &mut Context,
) -> BoundRefinement {
    // Find the small-model bounds of any combination of the literal
    let smp_bounds = match small_model_bounds(literals, fm, ctx) {
        Some(b) => b,
        None => return BoundRefinement::SmallModelReached, // No satisfying assignment
    };

    let mut small_model_reached = true;
    let mut bounds = bounds.clone();

    // Update the bounds of the variables in literals based on the step function but clamp to the small-model bounds
    let vars = literals
        .iter()
        .flat_map(|l| l.variables())
        .collect::<IndexSet<_>>();
    for v in vars {
        // Check if the variable is bounded
        if let Some(current_bound) = bounds.get(&v) {
            let increased = step.apply(current_bound);
            let clamped = increased.intersect(smp_bounds.get(&v).unwrap());
            if clamped != current_bound {
                // changed
                small_model_reached = false;
            }
            // TODO: Check if the limit is reached
            bounds.set(v.clone(), clamped);
        }
    }

    if small_model_reached {
        BoundRefinement::SmallModelReached
    } else {
        BoundRefinement::Refined(bounds)
    }
}

/// Computes the small-model bounds for any combinations given literals that can be satisfied by the formula.
fn small_model_bounds(literals: &[Literal], fm: &Formula, ctx: &mut Context) -> Option<Bounds> {
    // Split literals into entailed and not entailed
    let (entailed, not_entailed): (Vec<_>, Vec<_>) = literals.iter().partition(|l| fm.entails(l));

    let mut base_inferer = BoundInferer::default();
    for l in entailed {
        base_inferer.add_literal(l.clone(), ctx);
    }
    // The bounds of the conjunction of all entailed literals.
    // If these are conflicting, then any combination of literals is conflicting.
    let base_bounds = base_inferer.infer()?;

    // Build all possible combinations of the entailed literals.
    // That it, compute the subset of the power set of the literals such that each subset contains all entailed literals.
    // For each combination compute the small-model bounds.
    let mut combinations = Vec::with_capacity(2usize.pow(not_entailed.len() as u32 + 1));
    combinations.push((base_inferer, base_bounds));

    // Dynamic programming to build the combinations.
    // We filter out any combination that is conflicting.
    for l in not_entailed {
        let mut new_combinations = Vec::new();
        for (inferer, _) in &combinations {
            let mut new_inferer = inferer.clone();
            new_inferer.add_literal(l.clone(), ctx);
            if let Some(bounds) = new_inferer.infer() {
                new_combinations.push((new_inferer, bounds));
            }
        }
        combinations.extend(new_combinations);
    }

    // There are no combinations with non-conflicting bounds.
    if combinations.is_empty() {
        None
    } else {
        // For each variable, take the minimum of the lower bounds and the maximum of the upper bounds.
        let mut smp_bounds = Bounds::default();
        for (_, bounds) in combinations {
            for (v, b) in bounds.iter() {
                match smp_bounds.get(v) {
                    Some(existings) => {
                        let lower = std::cmp::min(existings.lower(), b.lower());
                        let upper = std::cmp::max(existings.upper(), b.upper());
                        smp_bounds.set(v.clone(), Interval::new(lower, upper));
                    }
                    None => {
                        smp_bounds.set(v.clone(), b.clone());
                    }
                }
            }
        }
        Some(smp_bounds)
    }
}
