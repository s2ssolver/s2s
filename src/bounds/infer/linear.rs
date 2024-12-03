//! Linear Bound Refinement

use std::{collections::HashMap, rc::Rc};

use indexmap::IndexSet;

use crate::{
    bounds::{BoundValue, Bounds},
    canonical::{
        ArithOperator, LinearArithTerm, LinearConstraint, LinearSummand, Symbol, WordEquation,
    },
    node::{Sorted, Variable},
};

use super::InferringStrategy;

/// Implements a the iterative linear bound refinement algorithm.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinearRefiner {
    /// The linear constraints to refine the bounds with. Wrapped in an Rc to make cloning cheap.
    linears: IndexSet<Rc<LinearConstraint>>,
    conflict: bool,
}

impl LinearRefiner {
    /// Adds a linear constraint to the refiner.
    pub fn add_linear(&mut self, mut linear: LinearConstraint) {
        // canonicalize the linear constraint before adding it
        linear.canonicalize();
        match linear.operator() {
            ArithOperator::Ineq | ArithOperator::Eq => {
                let leq =
                    LinearConstraint::new(linear.lhs().clone(), ArithOperator::Leq, linear.rhs());
                let geq =
                    LinearConstraint::new(linear.lhs().clone(), ArithOperator::Geq, linear.rhs());
                if linear.operator() == ArithOperator::Ineq {
                    // can only check for conflicts if the operator is an inequality
                    // if both the leq and the geq are present, we have a conflict because then lhs = rhs and lhs != rhs.
                    if self.linears.contains(&Rc::new(leq)) && self.linears.contains(&Rc::new(geq))
                    {
                        self.conflict = true;
                    }
                } else {
                    // if the operator is an equality, we can just add both the leq and the geq
                    self.add_linear(leq);
                    self.add_linear(geq);
                }
            }
            ArithOperator::Leq
            | ArithOperator::Less
            | ArithOperator::Geq
            | ArithOperator::Greater => {
                let flipped = linear.negate();
                if self.linears.contains(&Rc::new(flipped)) {
                    self.conflict = true;
                }
                self.linears.insert(Rc::new(linear));
            }
        }
    }

    /// Adds a word equation to the refiner.
    pub fn add_weq(&mut self, weq: &WordEquation) {
        self.add_linear(length_abstraction(weq));
    }

    /// Refines the bounds of the given variables.
    /// If a variable is not present in the bounds, it is considered unbounded (i.e., the bounds are (-inf, inf)).
    /// If a conflict is detected, i.e., if the linear constraints are unsatisfiable, `None` is returned.
    pub fn refine(&mut self, bounds: &Bounds) -> Option<Bounds> {
        if self.conflict {
            return None;
        }

        let mut changed = true;
        let mut refined = bounds.clone();
        while changed {
            changed = false;
            for linear in &self.linears {
                if let Some(new_bounds) = self.refinement_step(&refined, linear) {
                    if self.any_empty(&new_bounds) {
                        // the linear constraints are unsatisfiable
                        self.conflict = true;
                        return None;
                    }
                    refined = new_bounds;
                    changed = true;
                }
            }
        }
        Some(refined)
    }

    /// Checks if any of the bounds is empty.
    /// If this is the case, the linear constraints are unsatisfiable.
    fn any_empty(&self, bounds: &Bounds) -> bool {
        for (_, b) in bounds.iter() {
            if b.is_empty() {
                return true;
            }
        }
        false
    }

    fn refinement_step(&self, bounds: &Bounds, linear: &LinearConstraint) -> Option<Bounds> {
        let mut new_bounds = bounds.clone();
        let mut changed = false;
        log::trace!("Refining bounds {} w.r.t. {}", bounds, linear);
        for var in linear.variables() {
            let (op, term, divisor) = self.solve_for(linear, &var);
            log::trace!("\t {} {} ({}) / {}", var, op, term, divisor);
            match op {
                ArithOperator::Less | ArithOperator::Leq => {
                    if let BoundValue::Num(largest) = self.eval_largest(&term, bounds) {
                        if let Some(dived) = largest.checked_div(divisor as i32) {
                            let dived = if ArithOperator::Less == op {
                                BoundValue::Num(dived - 1)
                            } else {
                                BoundValue::Num(dived)
                            };
                            log::trace!("\t\t {op} {dived}");
                            if dived < self.ub(var.as_ref(), bounds) {
                                changed = true;
                                new_bounds.set_upper(var.as_ref(), dived);
                            }
                        }
                    }
                }
                ArithOperator::Greater | ArithOperator::Geq => {
                    if let BoundValue::Num(smallest) = self.eval_smallest(&term, bounds) {
                        if let Some(dived) = smallest.checked_div(divisor as i32) {
                            let dived = if ArithOperator::Greater == op {
                                BoundValue::Num(dived + 1)
                            } else {
                                BoundValue::Num(dived)
                            };
                            log::trace!("\t\t {op} {dived}");

                            if dived > self.lb(var.as_ref(), bounds) {
                                changed = true;
                                new_bounds.set_lower(var.as_ref(), dived);
                            }
                        }
                    }
                }
                _ => (),
            }
        }
        if changed {
            Some(new_bounds)
        } else {
            None
        }
    }

    /// Solves the given linear constraint for the given variable `var``.
    /// Returns a tuple `(op, term, divisor)`` such that the given constraint is equivalend to
    /// `var op (term / divisor)`.
    /// The divisor is always positive.
    fn solve_for(
        &self,
        lc: &LinearConstraint,
        var: &Rc<Variable>,
    ) -> (ArithOperator, LinearArithTerm, usize) {
        let mut divisor = 0;
        let mut dividend = LinearArithTerm::from_const(lc.rhs());
        for t in lc.lhs().iter() {
            match t {
                LinearSummand::Const(_) => dividend.add_summand(t.flip_sign()),
                LinearSummand::Mult(v, coeff) if v.variable() == var => divisor += coeff,
                LinearSummand::Mult(_, _) => dividend.add_summand(t.flip_sign()),
            }
        }

        if divisor < 0 {
            // If we have an inequality and the divisor is negative, we need to 'flip' the operator.
            let op = match lc.operator() {
                ArithOperator::Eq => ArithOperator::Eq,
                ArithOperator::Ineq => ArithOperator::Ineq,
                _ => lc.operator().flip(),
            };
            // We also need to negate both the divisor and the dividend to make the division positive.
            dividend.multiply_constant(-1);
            (op, dividend, divisor.unsigned_abs() as usize)
        } else if divisor > 0 {
            (lc.operator(), dividend, divisor as usize)
        } else {
            // if the divisor is zero, then the variable is not present in the constraint.
            // This is a precondition violation.
            unreachable!("Variable {} not present in constraint {}", var, lc)
        }
    }

    /// Returns the lower bound of the given variable.
    fn lb(&self, var: &Variable, bounds: &Bounds) -> BoundValue {
        match bounds.get_lower(var) {
            Some(b) => b,
            None => {
                if var.sort().is_string() {
                    0.into()
                } else {
                    BoundValue::NegInf
                }
            }
        }
    }

    /// Returns the upper bound of the given variable.
    fn ub(&self, var: &Variable, bounds: &Bounds) -> BoundValue {
        match bounds.get_upper(var) {
            Some(b) => b,
            None => BoundValue::PosInf,
        }
    }

    /// Evaluates the smallest possible value of the given term under the given bounds.
    fn eval_smallest(&self, term: &LinearArithTerm, bounds: &Bounds) -> BoundValue {
        let mut smallest = 0;
        for t in term.iter() {
            match t {
                LinearSummand::Const(c) => smallest += c,
                LinearSummand::Mult(v, coeff) => {
                    if *coeff >= 0 {
                        // Add the smallest possible value of the variable
                        let lb = self.lb(v.variable().as_ref(), bounds);
                        match lb * (*coeff).into() {
                            BoundValue::Num(v) => {
                                if let Some(v) = smallest.checked_add(v as i64) {
                                    smallest = v;
                                } else {
                                    return BoundValue::PosInf;
                                }
                            }
                            _ => {
                                return BoundValue::NegInf;
                            }
                        }
                    } else {
                        // Subtract the largest possible value of the variable
                        let ub = self.ub(v.variable().as_ref(), bounds);
                        match ub * (*coeff).into() {
                            BoundValue::Num(v) => {
                                if let Some(v) = smallest.checked_add(v as i64) {
                                    smallest = v;
                                } else {
                                    return BoundValue::NegInf;
                                }
                            }
                            _ => return BoundValue::NegInf,
                        }
                    }
                }
            }
        }
        smallest.into()
    }

    /// Evaluates the largest possible value of the given term under the given bounds.
    fn eval_largest(&self, term: &LinearArithTerm, bounds: &Bounds) -> BoundValue {
        let mut largest = 0;
        for t in term.iter() {
            match t {
                LinearSummand::Const(c) => largest += c,
                LinearSummand::Mult(v, coeff) => {
                    if *coeff >= 0 {
                        // add the greatest possible value of the variable
                        let ub = self.ub(v.variable().as_ref(), bounds);
                        match ub * (*coeff).into() {
                            BoundValue::Num(v) => {
                                if let Some(v) = largest.checked_add(v as i64) {
                                    largest = v;
                                } else {
                                    return BoundValue::PosInf;
                                }
                            }
                            _ => return BoundValue::PosInf,
                        }
                    } else {
                        // subtract the least possible value of the variable
                        let lb = self.lb(v.variable().as_ref(), bounds);
                        match lb * (*coeff).into() {
                            BoundValue::Num(v) => {
                                if let Some(v) = largest.checked_add(v as i64) {
                                    largest = v;
                                } else {
                                    return BoundValue::PosInf;
                                }
                            }
                            _ => {
                                if v.variable().sort().is_string() {
                                    return 0.into();
                                } else {
                                    return BoundValue::PosInf;
                                }
                            }
                        }
                    }
                }
            }
        }
        largest.into()
    }
}

/// Derives a linear constraint from a word equation.
/// Every assignment of the variables that satisfies the word equation also satisfies the linear constraint.
/// The other way around is not necessarily true.
pub fn length_abstraction(weq: &WordEquation) -> LinearConstraint {
    let mut var_occurrences = HashMap::new();
    let mut constant_counter = 0;
    let lhs = weq.lhs();
    let rhs = weq.rhs();
    for s in lhs.symbols() {
        match s {
            Symbol::Variable(v) => {
                let counter = var_occurrences.entry(v).or_insert(0);
                *counter += 1;
            }
            Symbol::Constant(_) => {
                constant_counter -= 1;
            }
        }
    }
    for s in rhs.symbols() {
        match s {
            Symbol::Variable(v) => {
                let counter = var_occurrences.entry(v).or_insert(0);
                *counter -= 1;
            }
            Symbol::Constant(_) => {
                constant_counter += 1;
            }
        }
    }

    let mut lhs = LinearArithTerm::new();
    for (v, c) in var_occurrences {
        lhs.add_summand(LinearSummand::len_variable(v.clone(), c));
    }
    LinearConstraint::new(lhs, ArithOperator::Eq, constant_counter)
}

impl InferringStrategy for LinearRefiner {
    fn infer(&mut self) -> Option<Bounds> {
        self.refine(&Bounds::default())
    }

    fn conflict(&self) -> bool {
        self.conflict
    }
}

//     /// Derive a linear constraint that restricts the upper bound for the patter from a regular constraint, if the regular language is finite.
//     /// The constraint is of the form `lhs <= rhs`, where `lhs` is the length of the pattern (i.e., the sum of the lenght all variable occurrences plus the length of the constant symbols) and `rhs` is the number of states in the automaton.
//     /// Note that there cannot be a word in the (finite) language that is longer than the number of states.
//     /// If the regular language is not finite, `None` is returned.
//     pub fn from_regular_constraint_upper(re: &RegularConstraint) -> Option<Self> {
//         if let Some(automaton) = re.get_automaton() {
//             if !automaton.acyclic() {
//                 return None;
//             }

//             let mut lhs = LinearArithTerm::new();
//             let mut rhs = 0;

//             for x in re.get_pattern().iter() {
//                 match x {
//                     Symbol::Constant(_) => rhs -= 1,
//                     Symbol::Variable(v) => {
//                         lhs.add_var_coeff(&v.len_var().unwrap(), 1);
//                     }
//                 }
//             }

//             rhs += re.get_automaton().unwrap().states().len() as isize;

//             Some(Self {
//                 lhs,
//                 rhs,
//                 typ: LinearOperator::Leq,
//             })
//         } else {
//             None
//         }
//     }

//     /// Derive a linear constraint that restricts the lower bound for the pattern from a regular constraint.
//     /// The constraint is of the form `lhs >= rhs`, where `lhs` is the length of the pattern (i.e., the sum of the lenght all variable occurrences plus the length of the constant symbols) and `rhs` is the shortest path from the initial state to a final state in the automaton.
//     pub fn from_regular_constraint_lower(re: &RegularConstraint) -> Self {
//         let automaton = re.get_automaton().unwrap();
//         let mut lhs = LinearArithTerm::new();
//         let mut rhs = 0;

//         for x in re.get_pattern().iter() {
//             match x {
//                 Symbol::Constant(_) => rhs -= 1,
//                 Symbol::Variable(v) => {
//                     lhs.add_var_coeff(&v.len_var().unwrap(), 1);
//                 }
//             }
//         }

//         rhs += automaton.shortest().unwrap_or(0) as isize;

//         Self {
//             lhs,
//             rhs,
//             typ: LinearOperator::Geq,
//         }
//     }
// }

// impl From<(LinearArithTerm, LinearArithTerm, LinearOperator)> for LinearConstraint {
//     fn from(value: (LinearArithTerm, LinearArithTerm, LinearOperator)) -> Self {
//         let lhs = value.0;
//         let rhs = value.1;
//         let typ = value.2;
//         if let Some(mut c) = rhs.is_constant() {
//             let mut lhs = lhs;
//             lhs.normalize();
//             let mut consts = vec![];
//             for fac in lhs.iter() {
//                 match fac {
//                     Summand::VarCoeff(_, _) => {}
//                     Summand::Const(c2) => {
//                         consts.push(fac.clone());
//                         c -= c2;
//                     }
//                 }
//             }
//             for fac in consts {
//                 lhs.remove_factor(&fac);
//             }
//             Self { lhs, rhs: c, typ }
//         } else {
//             let mut lhs = lhs.subtract(&rhs);
//             lhs.normalize();
//             let mut consts = vec![];
//             let mut c = 0;
//             for fac in lhs.iter() {
//                 match fac {
//                     Summand::VarCoeff(_, _) => {}
//                     Summand::Const(c2) => {
//                         consts.push(fac.clone());
//                         c -= c2;
//                     }
//                 }
//             }
//             for fac in consts {
//                 lhs.remove_factor(&fac);
//             }

//             Self { lhs, rhs: c, typ }
//         }
//     }
// }
