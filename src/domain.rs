use std::{fmt::Display, rc::Rc};

use indexmap::IndexMap;

use crate::{
    context::{Sorted, Variable},
    interval::Interval,
};

/// The Domain of a variable
/// For integer variables, the domain is an interval of all integer numbers the variable can assume.
/// For string variables,  the domain is an interval of all integer numbers of all possible lengths the variable can assume (i.e., the length of the string).
/// For Boolean variables, the domain is simply Bool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VarDomain {
    /// Range of the integer variable
    Int(Interval),
    /// Length of the string
    String(Interval),
    Bool,
}

impl Display for VarDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VarDomain::Int(interval) | VarDomain::String(interval) => write!(f, "{}", interval),
            VarDomain::Bool => write!(f, "Bool"),
        }
    }
}

/// The domain of all variables in the formula.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Domain {
    domains: IndexMap<Rc<Variable>, VarDomain>,
}

impl Domain {
    pub fn empty() -> Self {
        Self::default()
    }

    /// Sets the domain of a variable.
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
    fn set(&mut self, var: Rc<Variable>, dom: VarDomain) -> Option<VarDomain> {
        self.domains.insert(var, dom)
    }

    pub fn set_string(&mut self, var: Rc<Variable>, interval: Interval) -> Option<VarDomain> {
        debug_assert!(var.sort().is_string());
        self.set(var, VarDomain::String(interval))
    }

    pub fn set_int(&mut self, var: Rc<Variable>, interval: Interval) -> Option<VarDomain> {
        debug_assert!(var.sort().is_int());
        self.set(var, VarDomain::Int(interval))
    }

    /// Registers a Boolean variable.
    pub fn set_bool(&mut self, var: Rc<Variable>) {
        debug_assert!(var.sort().is_bool());
        self.set(var, VarDomain::Bool);
    }

    /// Returns the bound of a variable.
    /// If the variable is not present in the bounds, returns `None`.
    pub fn get(&self, var: &Variable) -> Option<VarDomain> {
        self.domains.get(var).copied()
    }

    /// Returns the interval of an integer variable.
    /// If the variable is not present in the bounds or the variable is not an integer variable, returns `None`.
    pub fn get_int(&self, var: &Variable) -> Option<Interval> {
        self.get(var).and_then(|d| match d {
            VarDomain::Int(i) => Some(i),
            _ => None,
        })
    }

    /// Returns the length interval of a string variable.
    /// If the variable is not present in the bounds or the variable is not a string variable, returns `None`.
    pub fn get_string(&self, var: &Variable) -> Option<Interval> {
        self.get(var).and_then(|d| match d {
            VarDomain::String(i) => Some(i),
            _ => None,
        })
    }

    // /// Returns the upper bound of a variable.
    // /// If the variable is not present in the bounds, returns `None`.
    // pub fn get_upper(&self, var: &Variable) -> Option<BoundValue> {
    //     self.get(var).map(|i| i.upper())
    // }

    // /// Returns the upper bound of the variable as a finite integer.
    // /// If the variable is not present in the bounds or the upper bound is not finite, returns `None`.
    // pub fn get_upper_finite(&self, var: &Variable) -> Option<i32> {
    //     self.get_upper(var).and_then(|b| b.as_num())
    // }

    // /// Returns the lower bound of a variable.
    // pub fn get_lower(&self, var: &Variable) -> Option<BoundValue> {
    //     self.get(var).map(|i| i.lower())
    // }

    // /// Returns the lower bound of the variable as a finite integer.
    // /// If the variable is not present in the bounds or the lower bound is not finite, returns `None`.
    // pub fn get_lower_finite(&self, var: &Variable) -> Option<i32> {
    //     self.get_lower(var).and_then(|b| b.as_num())
    // }

    /// Removes the bound of a variable.
    /// If the variable is not present in the bounds, returns `None`.
    /// Otherwise, returns the bound of the variable that was removed.
    #[cfg(test)]
    pub fn remove(&mut self, var: &Variable) -> Option<VarDomain> {
        self.domains.remove(var)
    }

    /// Returns the number of variables in the bounds.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.domains.len()
    }

    /// Returns true if the bounds are empty and false otherwise.
    /// The bounds are considered empty if there are no variables in the bounds.
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.domains.is_empty()
    }

    /// Returns an iterator over the string variables and their length bounds.
    pub fn iter_string(&self) -> impl Iterator<Item = (&Rc<Variable>, &Interval)> {
        self.domains.iter().filter_map(|(var, dom)| match dom {
            VarDomain::String(interval) => Some((var, interval)),
            _ => None,
        })
    }

    /// Returns an iterator over the integer variables and their bounds.
    pub fn iter_int(&self) -> impl Iterator<Item = (&Rc<Variable>, &Interval)> {
        self.domains.iter().filter_map(|(var, dom)| match dom {
            VarDomain::Int(interval) => Some((var, interval)),
            _ => None,
        })
    }

    /// Returns an iterator over the Boolean variables.
    pub(crate) fn iter_bool(&self) -> impl Iterator<Item = &Rc<Variable>> {
        self.domains
            .iter()
            .filter(|(var, dom)| var.sort().is_bool() && **dom == VarDomain::Bool)
            .map(|(var, _)| var)
    }

    //  /// Sets the upper bound of a variable to the given value `u`.
    // ///
    //  /// If the variable is not present in the bounds, sets the bounds to
    // /// - [-∞, u] if `u` is var is of sort `Sort::Int`
    // /// - [0, u] if `u` is of sort `Sort::String`
    // /// and returns `None`.
    // ///
    // /// If the variable is present in the bounds, sets the upper bound to `u` and returns the previous upper bound.
    // pub fn set_upper(&mut self, var: &Rc<Variable>, u: BoundValue) -> Option<BoundValue> {
    //     if let Some(interval) = self.get(var) {
    //         let prev_upper = interval.upper();
    //         self.set(var.clone(), Interval::new(interval.lower(), u));
    //         Some(prev_upper)
    //     } else {
    //         let lower = match var.sort() {
    //             Sort::Int => BoundValue::NegInf,
    //             Sort::String => BoundValue::Num(0),
    //             _ => unreachable!("Variable {} of sort {} has no bounds", var, var.sort()),
    //         };
    //         self.set(var.clone(), Interval::new(lower, u));
    //         None
    //     }
    // }

    // /// Sets the lower bound of a variable to the given value `l`.
    // /// If the variable is not present in the bounds, sets the bounds [l, ∞] and returns `None`.
    // /// If the variable is present in the bounds, sets the lower bound to `l` and returns the previous lower bound.
    // pub fn set_lower(&mut self, var: &Rc<Variable>, l: BoundValue) -> Option<BoundValue> {
    //     if let Some(interval) = self.get(var) {
    //         let prev_lower = interval.lower();
    //         self.set(var.clone(), Interval::new(l, interval.upper()));
    //         Some(prev_lower)
    //     } else {
    //         self.set(var.clone(), Interval::new(l, BoundValue::PosInf));
    //         None
    //     }
    // }
}

impl Display for Domain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (var, domain) in &self.domains {
            write!(f, "{}: {}, ", var, domain)?;
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod test {

    use crate::context::Sort;

    use super::*;

    #[test]
    fn test_insert_and_get() {
        let mut interval_map = Domain::default();

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let var = Rc::new(var);
        let interval = Interval::new(1, 5);

        interval_map.set(var.clone(), VarDomain::String(interval));

        assert_eq!(
            interval_map.get(&var),
            Some(VarDomain::String(Interval::new(1, 5)))
        );
    }

    #[test]
    fn test_remove() {
        let mut interval_map = Domain::default();

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let var = Rc::new(var);
        let interval = Interval::new(1, 5);

        interval_map.set(var.clone(), VarDomain::String(interval));
        let removed = interval_map.remove(&var);

        assert_eq!(removed, Some(VarDomain::String(Interval::new(1, 5))));
        assert!(interval_map.get(&var).is_none());
    }

    #[test]
    fn test_len_and_is_empty() {
        let mut interval_map = Domain::default();

        assert_eq!(interval_map.len(), 0);
        assert!(interval_map.is_empty());

        let var = Variable::new(0, "x".to_string(), Sort::Int);
        let var = Rc::new(var);
        let interval = Interval::new(1, 5);

        interval_map.set(var, VarDomain::String(interval));

        assert_eq!(interval_map.len(), 1);
        assert!(!interval_map.is_empty());
    }
}
