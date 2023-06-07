use std::{cmp::min, fmt::Display};

use indexmap::IndexMap;

use crate::{
    formula::{Atom, Formula, Predicate},
    model::{
        linears::{LinearArithFactor, LinearConstraint},
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
    fn clamp_upper(&mut self, max_upper: isize) {
        match self {
            IntDomain::Bounded(_, u) => *u = min(*u, max_upper),
            IntDomain::LowerBounded(l) => *self = IntDomain::Bounded(*l, max_upper),
            IntDomain::UpperBounded(u) => *u = min(*u, max_upper),
            IntDomain::Unbounded => *self = IntDomain::UpperBounded(max_upper),
            IntDomain::Empty => {}
        }
    }

    fn intersect(&self, other: &Self) -> Self {
        todo!();
    }
}

/// Every integer variable is associated with a domain.
/// This includes length of string variables, which are implicitly viewed as integer variables.
/// By default, all integer variables are unbounded.
pub struct Bounds {
    domains: IndexMap<Variable, IntDomain>,
}

impl Bounds {
    pub fn new() -> Self {
        Self {
            domains: IndexMap::new(),
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
        self.domains.get(var).map_or(IntDomain::Unbounded, |d| *d)
    }

    pub fn infer(formla: &Formula, var_manager: &VarManager) -> Self {
        let mut bounds = Self::new();
        for str_var in var_manager.of_sort(crate::model::Sort::String, true) {
            bounds.set(&str_var.len_var(), IntDomain::LowerBounded(0));
        }
        for atom in formla.asserted_atoms() {
            match atom {
                Atom::Predicate(Predicate::WordEquation(eq)) => {
                    // Get the lin constraint and solve if only one variable
                    let lincon = LinearConstraint::from_word_equation(&eq);
                    println!("eq {} -> lincon: {}", eq, lincon);
                    if lincon.lhs().len() == 1 {
                        match &lincon.lhs()[0] {
                            LinearArithFactor::VarCoeff(v, x) => {
                                if *x == 0 {
                                    if lincon.rhs() != 0 {
                                        bounds.set(v, IntDomain::Empty);
                                    }
                                } else if lincon.rhs() % x == 0 {
                                    let new_bound = lincon.rhs() / x;
                                    // TODO: use bounds.get(v).intersect(IntDomain::Bounded(new_bound, new_bound))
                                    match bounds.get(v) {
                                        IntDomain::UpperBounded(u) | IntDomain::Bounded(_, u) => {
                                            if new_bound < u {
                                                bounds.set(
                                                    v,
                                                    IntDomain::Bounded(new_bound, new_bound),
                                                );
                                            } else {
                                                // Cannot satisfy both
                                                bounds.set(v, IntDomain::Empty);
                                            }
                                        }
                                        IntDomain::LowerBounded(l) => {
                                            if l <= new_bound {
                                                bounds.set(
                                                    v,
                                                    IntDomain::Bounded(new_bound, new_bound),
                                                );
                                            } else {
                                                // Cannot satisfy both
                                                bounds.set(v, IntDomain::Empty);
                                            }
                                        }
                                        IntDomain::Unbounded => {
                                            bounds.set(v, IntDomain::Bounded(new_bound, new_bound));
                                        }
                                        IntDomain::Empty => {}
                                    }
                                } else {
                                    bounds.set(v, IntDomain::Empty);
                                };
                            }
                            crate::model::linears::LinearArithFactor::Const(_) => {}
                        }
                    }
                }
                Atom::Predicate(_) => {
                    /* TODO: Linears
                        - EQ: Same as word equation
                        - LEQ: Use rhs as upper bound for each variable in lhs which has lower bound of 0
                    */
                }
                Atom::BoolVar(_) => todo!(),
            }
        }
        bounds
    }

    pub fn clamp(&mut self, limits: &Self) -> bool {
        todo!()
    }
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
        for (var, domain) in &self.domains {
            writeln!(f, "{}: {}", var, domain)?;
        }
        Ok(())
    }
}
