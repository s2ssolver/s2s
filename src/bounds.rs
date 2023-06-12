use std::{
    cmp::{max, min},
    fmt::Display,
};

use indexmap::IndexMap;

use crate::{
    formula::{Assignment, Atom, ConstVal, Formula, Predicate},
    model::{
        linears::{LinearArithFactor, LinearConstraint, LinearConstraintType},
        VarManager, Variable,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntDomain {
    /// Is bounded by an upper and lower bound (inclusive)
    Bounded(isize, isize),
    ///  Is bounded by a lower bound (inclusive)
    LowerBounded(isize),
    /// Is bounded by an upper bound (inclusive)
    UpperBounded(isize),
    /// Is unbounded
    Unbounded,
    /// Is empty
    Empty,
}

impl IntDomain {
    fn bounded(lower: isize, upper: isize) -> Self {
        if lower > upper {
            IntDomain::Empty
        } else {
            IntDomain::Bounded(lower, upper)
        }
    }

    fn fixed(value: isize) -> Self {
        IntDomain::Bounded(value, value)
    }

    pub fn upper(&self) -> Option<isize> {
        match self {
            IntDomain::Bounded(_, u) => Some(*u),
            IntDomain::LowerBounded(_) => None,
            IntDomain::UpperBounded(u) => Some(*u),
            IntDomain::Unbounded => None,
            IntDomain::Empty => None,
        }
    }

    pub fn lower(&self) -> Option<isize> {
        match self {
            IntDomain::Bounded(l, _) => Some(*l),
            IntDomain::LowerBounded(l) => Some(*l),
            IntDomain::UpperBounded(_) => None,
            IntDomain::Unbounded => None,
            IntDomain::Empty => None,
        }
    }

    pub fn set_upper(&mut self, upper: isize) {
        match self {
            IntDomain::UpperBounded(u) | IntDomain::Bounded(_, u) => *u = upper,
            IntDomain::LowerBounded(l) => *self = Self::bounded(*l, upper),
            IntDomain::Unbounded => *self = Self::UpperBounded(upper),
            IntDomain::Empty => {}
        }
    }

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
}

/// Every integer variable is associated with a domain.
/// This includes length of string variables, which are implicitly viewed as integer variables.
/// By default, all integer variables are unbounded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bounds {
    domains: IndexMap<Variable, IntDomain>,
    default: IntDomain,
}

impl Bounds {
    pub fn new() -> Self {
        Self {
            domains: IndexMap::new(),
            default: IntDomain::Unbounded,
        }
    }

    pub fn with_defaults(default: IntDomain) -> Self {
        Self {
            domains: IndexMap::new(),
            default,
        }
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
        self.domains.get(var).map_or(self.default, |d| *d)
    }

    /// Returns the upper bound of a variable.
    /// Returns `None` if the variable is unbounded.
    pub fn get_upper(&self, var: &Variable) -> Option<isize> {
        let u = self.get(var).upper();
        u
    }

    pub fn get_lower(&self, var: &Variable) -> Option<isize> {
        self.get(var).lower()
    }

    pub fn set_upper(&mut self, var: &Variable, upper: isize) {
        let mut domain = self.get(var);
        domain.set_upper(upper);
        self.set(var, domain);
    }

    pub fn infer(formla: &Formula, var_manager: &VarManager) -> Self {
        let mut bounds = Self::new();
        for str_var in var_manager.of_sort(crate::model::Sort::String, true) {
            bounds.set(&str_var.len_var(), IntDomain::LowerBounded(0));
        }
        let mut bound_prev = bounds.clone();
        let mut stop = false;
        while !stop {
            for atom in formla.asserted_atoms() {
                match atom {
                    Atom::Predicate(Predicate::WordEquation(eq)) => {
                        let lincon = LinearConstraint::from_word_equation(&eq);
                        let newbounds = lincon_upper_bound(&lincon, &bounds);
                        bounds = bounds.intersect(&newbounds);
                    }
                    Atom::Predicate(Predicate::LinearConstraint(lincon)) => {
                        let newbounds = lincon_upper_bound(&lincon, &bounds);
                        bounds = bounds.intersect(&newbounds);
                    }
                    Atom::False | Atom::True | Atom::BoolVar(_) | Atom::Predicate(_) => {}
                }
            }
            if bounds == bound_prev {
                // Nothing changed, stop here
                stop = true;
            } else {
                bound_prev = bounds.clone();
            }
        }
        bounds
    }

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
    pub fn uppers_leq(&self, val: isize) -> bool {
        self.domains
            .values()
            .all(|d| d.upper().map_or(false, |u| u <= val))
            && self.default.upper().map_or(false, |u| u <= val)
    }

    /// Returns true if all upper bounds are strictly less than the given value and false otherwise.
    pub fn uppers_le(&self, val: isize) -> bool {
        self.domains
            .values()
            .all(|d| d.upper().map_or(false, |u| u < val))
            && self.default.upper().map_or(false, |u| u < val)
    }

    /// Returns true if all upper bounds are greater than or  equal to the given value and false otherwise.
    pub fn uppers_geq(&self, val: isize) -> bool {
        self.domains
            .values()
            .all(|d| d.upper().map_or(true, |u| u >= val))
            && self.default.upper().map_or(true, |u| u >= val)
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
            if let Some(upper) = dom.upper() {
                let new_upper = updater(upper);

                if new_upper != upper {
                    dom.set_upper(new_upper);
                    any_changed = true;
                }
            }
        }
        if let Some(def_upper) = self.default.upper() {
            let new_default = updater(def_upper);
            if new_default != def_upper {
                self.default.set_upper(new_default);
                any_changed = true;
            }
        }
        any_changed
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

fn lincon_upper_bound(lincon: &LinearConstraint, bounds: &Bounds) -> Bounds {
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
                                            rhs_min.as_mut().map(|r| *r -= lb * other_coeff);
                                        } else {
                                            rhs_min = None;
                                        }
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            rhs_max.as_mut().map(|r| *r -= ub * other_coeff);
                                        } else {
                                            rhs_max = None;
                                        }
                                    } else {
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            rhs_min.as_mut().map(|r| *r -= ub * other_coeff);
                                        } else {
                                            rhs_min = None;
                                        }
                                        if let Some(lb) = bounds.get_lower(other_v) {
                                            rhs_max.as_mut().map(|r| *r -= lb * other_coeff);
                                        } else {
                                            rhs_max = None;
                                        }
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    rhs_min.as_mut().map(|r| *r -= c);
                                    rhs_max.as_mut().map(|r| *r -= c);
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
                                log::info!("{}: var {} upper bounded by {}", lincon, v, u);
                                new_bounds.set(v, IntDomain::UpperBounded(u));
                            }
                            (Some(l), None) => {
                                log::info!("{}: var {} lower bounded by {}", lincon, v, l);
                                new_bounds.set(v, IntDomain::LowerBounded(l));
                            }
                            (Some(l), Some(u)) => {
                                log::info!("{}: var {} bounded by [{},{}]", lincon, v, l, u);
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
                                            rhs_min.as_mut().map(|r| *r -= lb * other_coeff);
                                        } else {
                                            rhs_min = None;
                                        }
                                    } else {
                                        if let Some(ub) = bounds.get_upper(other_v) {
                                            rhs_min.as_mut().map(|r| *r -= ub * other_coeff);
                                        } else {
                                            rhs_min = None;
                                        }
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    rhs_min.as_mut().map(|r| *r -= c);
                                }
                            }
                        }

                        if *coeff >= 0 {
                            let new_upper = rhs_min.map(|r| r / coeff);

                            match new_upper {
                                None => {}
                                Some(u) => {
                                    log::info!("{}: var {} upper bounded by {}", lincon, v, u);
                                    new_bounds.set(v, IntDomain::UpperBounded(u));
                                }
                            }
                        } else {
                            let new_lower = rhs_min.map(|r| r / coeff);

                            match new_lower {
                                None => {}
                                Some(l) => {
                                    log::info!("{}: var {} lower bounded by {}", lincon, v, l);
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
                                            rhs_max.as_mut().map(|r| *r -= ub * other_coeff);
                                        } else {
                                            rhs_max = None;
                                        }
                                    } else {
                                        if let Some(lb) = bounds.get_lower(other_v) {
                                            rhs_max.as_mut().map(|r| *r -= lb * other_coeff);
                                        } else {
                                            rhs_max = None;
                                        }
                                    }
                                }
                                LinearArithFactor::Const(c) => {
                                    rhs_max.as_mut().map(|r| *r -= c);
                                }
                            }
                        }

                        if *coeff >= 0 {
                            let new_lower = rhs_max.map(|r| r / coeff);

                            match new_lower {
                                None => {}
                                Some(l) => {
                                    log::info!("{}: var {} lower bounded by {}", lincon, v, l);
                                    new_bounds.set(v, IntDomain::LowerBounded(l));
                                }
                            }
                        } else {
                            let new_upper = rhs_max.map(|r| r / coeff);

                            match new_upper {
                                None => {}
                                Some(u) => {
                                    log::info!("{}: var {} lower bounded by {}", lincon, v, u);
                                    new_bounds.set(v, IntDomain::UpperBounded(u));
                                }
                            }
                        }
                    }
                    LinearArithFactor::Const(_) => panic!("Linear constraint not in normal form"),
                }
            }
        }
    }

    new_bounds
}

impl Display for IntDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntDomain::Bounded(l, u) => {
                if l == u {
                    write!(f, "{}", l)
                } else if l < u {
                    write!(f, "[{}, {}]", l, u)
                } else {
                    write!(f, "∅")
                }
            }
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
