use indexmap::{IndexMap, IndexSet};

use regulaer::re::CharRegex;

use crate::{
    error::Error,
    instance::Instance,
    model::{
        constraints::{
            LinearArithFactor, LinearConstraint, LinearConstraintType, Pattern, RegularConstraint,
            RegularConstraintType, Symbol, WordEquation,
        },
        Constraint, Sort,
    },
};

use super::{Bounds, IntDomain};

struct ConstraintPartition {
    /// Constraints of the form `x \in R` and `x \notin R` where x is a variable and R is a regular language.
    regulars: Vec<RegularConstraint>,
    /// Linear constraints over integer variables and string lengths.
    linear: Vec<LinearConstraint>,
    /// Word equations over string variables.
    eqs: Vec<WordEquation>,
}

impl ConstraintPartition {
    fn contains_concat(&self) -> bool {
        for r in &self.regulars {
            if !r.single_var_pattern() {
                return true;
            }
        }
        for eq in &self.eqs {
            if let WordEquation::Generic { .. } = eq {
                return true;
            }
        }
        false
    }

    fn contains_linear(&self) -> bool {
        !self.linear.is_empty()
    }

    fn new(constraints: &[Constraint]) -> Self {
        let mut regulars = Vec::new();
        let mut linear = Vec::new();
        let mut eqs = Vec::new();
        for con in constraints {
            match con {
                Constraint::RegularConstraint(r) => regulars.push(r.clone()),
                Constraint::LinearConstraint(l) => linear.push(l.clone()),
                Constraint::WordEquation(e) => eqs.push(e.clone()),
            }
        }
        Self {
            regulars,
            linear,
            eqs,
        }
    }
}

/// Infers the bounds of conjunction of the given constraints.
/// If the conjunction of literals is satisfiable, then there is a solution that satisfies the inferred bounds.
pub fn infer_bounds(constraints: &[Constraint], instance: &Instance) -> Result<Bounds, Error> {
    let partition = ConstraintPartition::new(constraints);

    // Check which techniques can be used
    let mut inferred: Bounds = if !partition.contains_concat() && !partition.contains_linear() {
        let mut var_eqs = vec![];
        let mut regulars = vec![];
        for r in &partition.regulars {
            let r = r.clone();
            assert!(r.get_automaton().is_some());

            regulars.push(r);
        }
        for eq in &partition.eqs {
            match eq {
                WordEquation::Assignment { lhs, rhs, eq_type } => {
                    // Convert to regular constraint
                    let rtype = if eq_type.is_equality() {
                        RegularConstraintType::In
                    } else {
                        RegularConstraintType::NotIn
                    };
                    let re = RegularConstraint::new(
                        CharRegex::const_word(rhs),
                        Pattern::variable(lhs),
                        rtype,
                    );
                    regulars.push(re);
                }
                WordEquation::VarEquality { .. } => var_eqs.push(eq.clone()),
                WordEquation::Generic { .. } => unreachable!("No concatenation in partition"),
            }
        }

        from_regular_constraints(&regulars, &var_eqs, instance)?
    } else {
        // Use linear propagation method to find bounds, might be incomplete
        let mut linears = partition.linear.clone();
        for eq in &partition.eqs {
            linears.push(LinearConstraint::from_word_equation(eq));
        }
        for re in &partition.regulars {
            if re.get_type().is_in() {
                linears.push(LinearConstraint::from_regular_constraint_lower(re));
                if let Some(upper) = LinearConstraint::from_regular_constraint_upper(re) {
                    linears.push(upper);
                }
            }
        }
        from_linears(&linears)?
    };
    log::debug!("Inferred bounds: {}", inferred);
    // Set lower bound of string variables to 0, if they are unbouded from below
    for str_var in instance.vars_of_sort(Sort::String) {
        if inferred.get_lower(&str_var.len_var().unwrap()).is_none() {
            inferred.set_lower(&str_var.len_var().unwrap(), 0);
        }
    }

    Ok(inferred)
}

/// Tries to find bounds for a set of  constraints of the form "x \in R" where x is a variable and R is a regular language.
/// We can bound x by the number of states of the automaton that recognizes the intersection of all automata that x is constrained by.
/// TODO: Can be generalized to regular constraints in conjunction with constraints of the form `x=y`, `x!=y`, `x=w`, `x!=w` where w is a word.
fn from_regular_constraints(
    constraints: &[RegularConstraint],
    var_eqs: &[WordEquation],
    _instance: &Instance,
) -> Result<Bounds, Error> {
    let all_single_var = constraints
        .iter()
        .all(|c| c.get_pattern().len() == 1 && c.single_var_pattern());
    let mut res_bounds = Bounds::new();

    if !all_single_var {
        // Cannot infer anything
        return Ok(res_bounds);
    }

    // Partition the constraints by the variable they constrain
    let mut recon_partition = IndexMap::new();
    for constr in constraints {
        if let Some(Symbol::Variable(v)) = constr.get_pattern().first() {
            recon_partition
                .entry(v)
                .or_insert_with(IndexSet::new)
                .insert(constr);
        }
    }

    let mut propagated = true;
    while propagated {
        propagated = false;
        for eq in var_eqs {
            if let WordEquation::VarEquality { lhs, rhs, eq_type } = eq {
                if eq_type.is_equality() {
                    let empty = IndexSet::new();
                    let p_lhs = recon_partition.get(rhs).unwrap_or(&empty);
                    let p_rhs = recon_partition.get(lhs).unwrap_or(&empty);
                    let union = p_lhs.union(p_rhs);
                    let union_count = union.clone().count();
                    if union_count != p_lhs.len() || union_count != p_rhs.len() {
                        let as_set = union.cloned().collect::<IndexSet<_>>();
                        recon_partition.insert(lhs, as_set.clone());
                        recon_partition.insert(rhs, as_set);

                        // Something changed, so we need to propagate again
                        propagated = true;
                    }
                }
            }
        }
    }

    for (string_var, regs) in recon_partition.into_iter() {
        let len_var = &string_var.len_var().unwrap();

        // intersect all automata and use the number of states as upper bound
        let first = regs.first().unwrap();

        let mut res = first.get_automaton().unwrap().clone();

        if first.get_type().is_not_in() {
            res = res.complement()?;
        }

        // Simultaneously calculate the underapproximation by multiplying the number of states in each automaton
        // If we run into an error (e.g. complement is no supported), we use the approximation
        log::trace!("Current {} ({} states)", first.get_re(), res.states().len());

        let mut ok = true;

        for next in regs.iter().skip(1) {
            let mut nfa_next = next.get_automaton().unwrap().clone();

            if next.get_type().is_not_in() {
                nfa_next = nfa_next.complement()?;
            }

            log::trace!(
                "Intersecting with {} ({} states)",
                next.get_re(),
                nfa_next.states().len()
            );

            res = match res.intersect(&nfa_next) {
                Ok(a) => a,
                Err(e) => {
                    log::warn!("Could not intersect automata: {}", e,);
                    ok = false;
                    break;
                }
            };

            log::trace!("\t done ({} states)", res.states().len());
        }

        if !ok {
            log::warn!(
                "Did not infer bounds for {} due to privous error.",
                string_var
            );
        } else {
            log::info!("Found bound for {}: {}", string_var, res.states().len());
            res_bounds.set_upper(len_var, res.states().len() as isize);
            if let Some(s) = res.shortest() {
                res_bounds.set_lower(len_var, s as isize);
            }
        }
    }

    Ok(res_bounds)
}

fn from_linears(linears: &[LinearConstraint]) -> Result<Bounds, Error> {
    let mut bounds = Bounds::new();
    let mut fixpoint = false;
    while !fixpoint {
        let lastbounds = bounds.clone();

        // Infer bounds on the variables using the linear constraint that can be inferred
        for linear in linears {
            let newbounds = propagate_bounds(linear, &bounds);
            bounds = bounds.intersect(&newbounds);
        }

        fixpoint = lastbounds == bounds;
    }
    Ok(bounds)
}

/// Infers the domain of the variables of a linear constraint based on the bounds of the other variables.
fn propagate_bounds(lincon: &LinearConstraint, bounds: &Bounds) -> Bounds {
    // Get the lin constraint and solve if only one variable
    let mut new_bounds = Bounds::new();
    match lincon.typ {
        LinearConstraintType::Eq => {
            for factor in lincon.lhs().iter() {
                match factor {
                    LinearArithFactor::VarCoeff(v, coeff) => {
                        if *coeff == 0 {
                            continue;
                        }
                        // The minimum value of the rhs is the rhs - sum of lower bounds * coeff of other vars
                        let mut rhs_min = Some(lincon.rhs());
                        let mut rhs_max = Some(lincon.rhs());
                        for other_factor in lincon.lhs().iter() {
                            match other_factor {
                                LinearArithFactor::VarCoeff(other_v, other_coeff) => {
                                    if other_v == v {
                                        continue;
                                    }
                                    if *other_coeff >= 0 {
                                        if let Some(lb) = bounds.get_lower(other_v) {
                                            if let Some(r) = rhs_min.as_mut() {
                                                *r -= lb * other_coeff
                                            }
                                        } else {
                                            rhs_min = None;
                                        }
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            if let Some(r) = rhs_max.as_mut() {
                                                *r -= ub * other_coeff
                                            }
                                        } else {
                                            rhs_max = None;
                                        }
                                    } else {
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            if let Some(r) = rhs_min.as_mut() {
                                                *r -= ub * other_coeff
                                            }
                                        } else {
                                            rhs_min = None;
                                        }
                                        if let Some(lb) = bounds.get_lower(other_v) {
                                            if let Some(r) = rhs_max.as_mut() {
                                                *r -= lb * other_coeff
                                            }
                                        } else {
                                            rhs_max = None;
                                        }
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    if let Some(r) = rhs_max.as_mut() {
                                        *r -= c;
                                    }
                                    if let Some(r) = rhs_min.as_mut() {
                                        *r -= c;
                                    }
                                }
                            }
                        }

                        let mut new_upper = rhs_min.map(|r| r / coeff);

                        let mut new_lower = rhs_max.map(|r| r / coeff);

                        if *coeff < 0 {
                            std::mem::swap(&mut new_upper, &mut new_lower);
                        }
                        match (new_lower, new_upper) {
                            (None, None) => {}
                            (None, Some(u)) => {
                                log::trace!("{}: var {} upper bounded by {}", lincon, v, u);
                                new_bounds.set(v, IntDomain::UpperBounded(u));
                            }
                            (Some(l), None) => {
                                log::trace!("{}: var {} lower bounded by {}", lincon, v, l);
                                new_bounds.set(v, IntDomain::LowerBounded(l));
                            }
                            (Some(l), Some(u)) => {
                                log::trace!("{}: var {} bounded by [{},{}]", lincon, v, l, u);
                                new_bounds.set(v, IntDomain::Bounded(l, u));
                            }
                        }
                    }
                    LinearArithFactor::Const(_) => panic!("Linear constraint not in normal form"),
                }
            }
        }
        LinearConstraintType::Less | LinearConstraintType::Leq => {
            for factor in lincon.lhs().iter() {
                match factor {
                    LinearArithFactor::VarCoeff(v, coeff) => {
                        if *coeff == 0 {
                            continue;
                        }
                        // The minimum value of the rhs is the rhs - sum of lower bounds * coeff of other vars
                        let mut rhs_min = Some(lincon.rhs());
                        for other_factor in lincon.lhs().iter() {
                            match other_factor {
                                LinearArithFactor::VarCoeff(other_v, other_coeff) => {
                                    if other_v == v {
                                        continue;
                                    }
                                    if *other_coeff >= 0 {
                                        if let Some(lb) = bounds.get_lower(other_v) {
                                            if let Some(r) = rhs_min.as_mut() {
                                                *r -= lb * other_coeff
                                            }
                                        } else {
                                            rhs_min = None;
                                        }
                                    } else if let Some(ub) = bounds.get_upper(other_v) {
                                        if let Some(r) = rhs_min.as_mut() {
                                            *r -= ub * other_coeff;
                                        }
                                    } else {
                                        rhs_min = None;
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    if let Some(r) = rhs_min.as_mut() {
                                        *r -= c;
                                    }
                                }
                            }
                        }

                        if *coeff >= 0 {
                            let new_upper = rhs_min.map(|r| r / coeff);

                            match new_upper {
                                None => {}
                                Some(u) => {
                                    log::trace!("{}: var {} upper bounded by {}", lincon, v, u);
                                    new_bounds.set(v, IntDomain::UpperBounded(u));
                                }
                            }
                        } else {
                            let new_lower = rhs_min.map(|r| r / coeff);

                            match new_lower {
                                None => {}
                                Some(l) => {
                                    log::trace!("{}: var {} lower bounded by {}", lincon, v, l);
                                    new_bounds.set(v, IntDomain::LowerBounded(l));
                                }
                            }
                        }
                    }
                    LinearArithFactor::Const(_) => panic!("Linear constraint not in normal form"),
                }
            }
        }

        LinearConstraintType::Geq | LinearConstraintType::Greater => {
            for factor in lincon.lhs().iter() {
                match factor {
                    LinearArithFactor::VarCoeff(v, coeff) => {
                        if *coeff == 0 {
                            continue;
                        }
                        // The minimum value of the rhs is the rhs - sum of lower bounds * coeff of other vars
                        let mut rhs_max = Some(lincon.rhs());
                        for other_factor in lincon.lhs().iter() {
                            match other_factor {
                                LinearArithFactor::VarCoeff(other_v, other_coeff) => {
                                    if other_v == v {
                                        continue;
                                    }
                                    if *other_coeff >= 0 {
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            if let Some(r) = rhs_max.as_mut() {
                                                *r -= ub * other_coeff
                                            }
                                        } else {
                                            rhs_max = None;
                                        }
                                    } else if let Some(lb) = bounds.get_lower(other_v) {
                                        if let Some(r) = rhs_max.as_mut() {
                                            *r -= lb * other_coeff
                                        }
                                    } else {
                                        rhs_max = None;
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    if let Some(r) = rhs_max.as_mut() {
                                        *r -= c;
                                    }
                                }
                            }
                        }

                        if *coeff >= 0 {
                            let new_lower = rhs_max.map(|r| r / coeff);

                            match new_lower {
                                None => {}
                                Some(l) => {
                                    log::trace!("{}: var {} lower bounded by {}", lincon, v, l);
                                    new_bounds.set(v, IntDomain::LowerBounded(l));
                                }
                            }
                        } else {
                            let new_upper = rhs_max.map(|r| r / coeff);

                            match new_upper {
                                None => {}
                                Some(u) => {
                                    log::trace!("{}: var {} lower bounded by {}", lincon, v, u);
                                    new_bounds.set(v, IntDomain::LowerBounded(u));
                                }
                            }
                        }
                    }
                    LinearArithFactor::Const(_) => panic!("Linear constraint not in normal form"),
                }
            }
        }
        LinearConstraintType::Ineq => { /* Can'f infer anything */ }
    }

    new_bounds
}
