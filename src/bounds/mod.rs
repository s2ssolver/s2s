//! Module for computing the small model bounds of sets of literals.
//!
//! For a given conjunction of literals, the small model bounds are the length variables in a presumed smallest solution.
//! If the conjunction has a solution, then it also has a solution of the length variables that is bounded by the small model bounds.
//! If not solution exists within the bounds, then the conjunction is unsatisfiable.
//!
//! The bounds are not computed exactly, but rather over-approximated.
//! Depending on the fragment of the conjunction, the bounds are computed using different strategies.
//! Not for all fragments, the bounds can be computed.

mod linear;
mod regular;
use std::{fmt::Display, rc::Rc};

use indexmap::{IndexMap, IndexSet};
pub use linear::LinearRefiner;

use regular::RegularBoundsInferer;
use smallvec::smallvec;

use crate::{
    interval::BoundValue,
    node::{
        canonical::{
            ArithOperator, AtomKind, LinearArithTerm, LinearConstraint, LinearSummand, Literal,
            RegularConstraint, VariableTerm, WordEquation,
        },
        NodeManager, Sorted, Variable,
    },
};

use crate::interval::Interval;

/// Bounds for integer variables and string lengths.
/// This is used to infer the small model bounds of a (sub) formula.
/// Maps every variable to an interval that bounds the variable length.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Bounds {
    bounds: IndexMap<Rc<Variable>, Interval>,
}

impl Bounds {
    /// Sets the bounds of a variable to the given interval.
    pub fn set(&mut self, var: Rc<Variable>, bound: Interval) {
        self.bounds.insert(var, bound);
    }

    /// Obtains the bounds of a variable.
    /// Returns None if the variable is not present in the bounds.
    pub fn get(&self, var: &Variable) -> Option<Interval> {
        self.bounds.get(var).copied()
    }

    /// Obtains the upper bound of a variable.
    /// Returns None if the variable is not present in the bounds.
    pub fn get_upper(&self, var: &Variable) -> Option<BoundValue> {
        self.bounds.get(var).map(|i| i.upper())
    }

    /// Obtains the lower bound of a variable.
    /// Returns None if the variable is not present in the bounds.
    pub fn get_lower(&self, var: &Variable) -> Option<BoundValue> {
        self.bounds.get(var).map(|i| i.lower())
    }

    /// Sets the upper bound of a variable to the given value.
    /// If the variable is not present in the bounds, it is added with the given upper bounds and unbounded lower bound.
    /// If the variable is present in the bounds, the upper bound is set to the given value and the lower bound is unbounded.
    pub fn set_upper(&mut self, var: Rc<Variable>, upper: BoundValue) {
        let current = self
            .bounds
            .entry(var.clone())
            .or_insert(Interval::unbounded());
        let new = current.with_upper(upper);
        self.bounds.insert(var, new);
    }

    /// Sets the lower bound of a variable to the given value.
    /// If the variable is not present in the bounds, it is added with the given lower bounds and unbounded upper bound.
    /// If the variable is present in the bounds, the lower bound is set to the given value and the upper bound is unbounded.
    pub fn set_lower(&mut self, var: Rc<Variable>, lower: BoundValue) {
        let current = self
            .bounds
            .entry(var.clone())
            .or_insert(Interval::unbounded());
        let new = current.with_lower(lower);
        self.bounds.insert(var, new);
    }

    /// Returns an iterator over the bounds.
    /// The iterator yields tuples of the form (variable, interval).
    pub fn iter(&self) -> impl Iterator<Item = (&Rc<Variable>, &Interval)> {
        self.bounds.iter()
    }
}

impl Display for Bounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (v, i) in self.bounds.iter() {
            writeln!(f, "{}: {}", v, i)?;
        }
        Ok(())
    }
}

/// The fragment that a formula belongs to.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
enum Fragment {
    Empty,
    Reg,
    Weq(bool),
    Lin,
    RegWeq(bool),
    RegLin,
    WeqLin(bool),
    RegWeqLin(bool),
}

/// Helper struct to find the fragment of a formula.
/// This is used to determine which strategy to use for inferring the bounds.
/// The fragment is determined by the literals in the formula.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct FragmentFinder {
    // The set of variables that appear in an inequality
    ineq_vars: IndexSet<Rc<Variable>>,
    // The set of variables that appear in a proper word equation.
    weq_vars: IndexSet<Rc<Variable>>,
    /// The set of variables that appear in a regular constraint
    in_re_vars: IndexSet<Rc<Variable>>,
    /// The set of variables that appear in a linear constraint
    lin_vars: IndexSet<Rc<Variable>>,
}

impl FragmentFinder {
    pub fn and(&mut self, lit: &Literal) {
        let pol = lit.polarity();
        match lit.atom().kind() {
            AtomKind::InRe(inre) => {
                self.in_re_vars.insert(inre.lhs().clone());
            }
            AtomKind::WordEquation(weq) => {
                if !pol {
                    for v in weq.variables() {
                        self.ineq_vars.insert(v);
                    }
                }
                if let WordEquation::General(_, _) = weq {
                    self.weq_vars.extend(weq.variables());
                } else {
                    // x=y and x=w are handled as the regular constraint
                    self.in_re_vars.extend(weq.variables());
                }
            }
            AtomKind::FactorConstraint(refc) => {
                self.in_re_vars.insert(refc.of().clone());
            }
            AtomKind::Linear(lc) => {
                self.lin_vars.extend(lc.variables());
            }
            _ => (),
        }
    }

    /// Contains a regular constraint in any polarity
    pub fn has_regular(&self) -> bool {
        !self.in_re_vars.is_empty()
    }

    /// Contains linear constraints
    pub fn has_linear(&self) -> bool {
        !self.lin_vars.is_empty()
    }

    /// Contains proper word equations in any polarity
    pub fn has_weq(&self) -> bool {
        !self.weq_vars.is_empty()
    }

    /// Contains proper word equations with negated polarity
    /// This is the case if theres at least one variable that appears in both a (proper) word equation and an inequality
    /// For example, if we have `abX = Y` and `Y != cd`, then `Y` appears in both a word equation and an inequality and thus this method returns true.
    /// If we only have `X = Y` and `Y != cd`, then this method returns false.
    /// Specifically, if there is no word equation in the fragment, then this method returns always false.
    pub fn has_negated_weq(&self) -> bool {
        self.ineq_vars.iter().any(|v| self.weq_vars.contains(v))
    }

    pub fn get_fragment(&self) -> Fragment {
        match (self.has_regular(), self.has_weq(), self.has_linear()) {
            (false, false, false) => Fragment::Empty,
            (true, false, false) => Fragment::Reg,
            (false, true, false) => Fragment::Weq(self.has_negated_weq()),
            (false, false, true) => Fragment::Lin,
            (true, true, false) => Fragment::RegWeq(self.has_negated_weq()),
            (true, false, true) => Fragment::RegLin,
            (false, true, true) => Fragment::WeqLin(self.has_negated_weq()),
            (true, true, true) => Fragment::RegWeqLin(self.has_negated_weq()),
        }
    }
}

/// Infers bounds for a set of literals.
#[derive(Debug, Default, Clone)]
pub struct BoundInferer {
    /// The set of literals for which we infer bounds
    literals: IndexSet<Literal>,
    /// Set to true if literals contain a conflict, i.e., a literal and its negation
    conflict: bool,

    /// The fragment of the literals
    fragment: FragmentFinder,

    /// The bounds inferer for regular constraints contained in the literals
    reg: RegularBoundsInferer,

    /// The fragment of the literals
    lin: LinearRefiner,
}

impl BoundInferer {
    fn add_reg(&mut self, reg: &RegularConstraint, pol: bool, mngr: &mut NodeManager) {
        let v = reg.lhs().clone();
        let re = reg.re().clone();
        self.reg.add_reg(v, re, pol, mngr);
    }

    fn add_weq(&mut self, weq: &WordEquation, pol: bool, mngr: &mut NodeManager) {
        match weq {
            WordEquation::ConstantEquality(_, _) => (),
            WordEquation::VarEquality(l, r) => {
                self.reg.add_var_eq(l.clone(), r.clone(), pol);
            }
            WordEquation::VarAssignment(l, r) => {
                self.reg.add_const_eq(l.clone(), r.clone(), pol, mngr);
            }
            WordEquation::General(_, _) => {}
        }
        if pol {
            self.lin.add_weq(weq)
        }
    }

    fn add_linear_constraint(&mut self, lc: &LinearConstraint) {
        self.lin.add_linear(lc.clone());
    }

    /// Adds a literal to the bounds inferer.
    /// This will add the literal to the set of literals for which we infer bounds.
    pub fn add_literal(&mut self, lit: Literal, mngr: &mut NodeManager) {
        self.literals.insert(lit.clone());

        self.conflict |= self.literals.contains(&lit.inverted());

        // skip this if there is a conflict
        let pol = lit.polarity();
        match lit.atom().kind() {
            AtomKind::Boolvar(_) => (),
            AtomKind::InRe(reg) => self.add_reg(reg, pol, mngr),
            AtomKind::WordEquation(weq) => self.add_weq(weq, pol, mngr),
            AtomKind::FactorConstraint(rfac) => {
                let re = rfac.as_regex(mngr);
                self.reg.add_reg(rfac.of().clone(), re, pol, mngr);
            }
            AtomKind::Linear(lc) => {
                let lc = if pol { lc.clone() } else { lc.negate() };

                if let Some(as_reg) = lc_to_reg(&lc, mngr) {
                    // also add the same constraint as a regular constraint
                    // that can help to converge faster in some cases
                    self.add_reg(&as_reg, true, mngr);
                }

                self.add_linear_constraint(&lc)
            }
        }
        self.fragment.and(&lit);
    }

    /// Returns true if the literals contain a conflict, i.e., a literal and its negation.
    fn conflicting(&self) -> bool {
        self.conflict || self.reg.conflict() || self.lin.conflict()
    }

    /// Infers the bounds of the variables in the literals.
    /// Depending on the fragment of the literals, different strategies are used to infer the bounds.
    /// It is not guaranteed that the bounds are exact, or are even computed for all variables.
    /// If the bounds on a variable cannot be computed, the variable is set to unbounded, i.e. the bounds are set to `(-inf, inf)`.
    ///
    /// If the set of literals is conflicting, i.e., has no valid bounds, then None is returned.
    /// In that case, the conjunction of the literals is unsatisfiable.
    pub fn infer(&mut self) -> Option<Bounds> {
        if self.conflicting() {
            return None;
        }

        let frag = self.fragment.get_fragment();

        let bounds = match frag {
            Fragment::Empty => Some(Bounds::default()),
            Fragment::Reg => self.reg.infer(),
            Fragment::Weq(_) => {
                // TODO: check straight-line fragment if no inequalities are present
                self.lin.infer()
            }
            Fragment::WeqLin(_) => self.lin.infer(),
            Fragment::Lin => self.lin.infer(),
            Fragment::RegWeq(false) | Fragment::RegLin | Fragment::RegWeqLin(false) => {
                for (v, nfa) in self.reg.iter_intersections() {
                    if nfa.is_empty() {
                        self.conflict = true;
                        return None;
                    } else {
                        if let Some(max) = nfa.longest_path() {
                            // This is none if the nfa contains cycles
                            // Add "|v| <= max" to the bounds
                            let lhs = LinearArithTerm::from_var(v.clone());
                            let lc = LinearConstraint::new(lhs, ArithOperator::Leq, max as i64);
                            self.lin.add_linear(lc);
                        }
                        if let Some(min) = nfa.shortest_path() {
                            // Add "|v| >= max" to the bounds
                            let lhs = LinearArithTerm::from_var(v.clone());
                            let lc = LinearConstraint::new(lhs, ArithOperator::Geq, min as i64);
                            self.lin.add_linear(lc);
                        } else {
                            // The automaton is empty, there is no solution
                            self.conflict = true;
                        }
                    }
                }

                self.lin.infer()
            }
            Fragment::RegWeqLin(true) | Fragment::RegWeq(true) => self.lin.infer(),
        };
        if let Some(mut b) = bounds {
            self.sanitize_bounds(&mut b);
            Some(b)
        } else {
            self.conflict = true;
            None
        }
    }

    /// Ensures that all string and int variables occurring in any of the literals are present in the bounds.
    /// If a variable is not present in the bounds, it is set to unbounded.
    fn sanitize_bounds(&mut self, bounds: &mut Bounds) {
        for v in self
            .literals
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().is_string() || v.sort().is_int())
        {
            if bounds.get(v.as_ref()).is_none() {
                if v.sort().is_string() {
                    bounds.set(v.clone(), Interval::bounded_below(0));
                } else {
                    bounds.set(v.clone(), Interval::unbounded());
                }
            }
        }
    }
}

fn lc_to_reg(lc: &LinearConstraint, mngr: &mut NodeManager) -> Option<RegularConstraint> {
    if lc.lhs().len() == 1 {
        if let LinearSummand::Mult(VariableTerm::Len(x), s) = lc.lhs().iter().next().unwrap() {
            // This is a constraint of the form `s|x| # rhs`, we can rewrite this as a regular constraint
            let (r, op, s) = match (lc.rhs() >= 0, *s >= 0) {
                (true, true) => (lc.rhs() as u32, lc.operator(), *s as u32),
                (false, false) if lc.operator() != ArithOperator::Eq => {
                    (-lc.rhs() as u32, lc.operator().flip(), -*s as u32)
                }
                (false, false) if lc.operator() == ArithOperator::Eq => {
                    (-lc.rhs() as u32, lc.operator(), -*s as u32)
                }
                _ => return None,
            };
            let builder = mngr.re_builder();
            let re = match op {
                ArithOperator::Eq => {
                    if r % s == 0 {
                        builder.pow(builder.allchar(), r / s)
                    } else {
                        builder.none()
                    }
                }
                ArithOperator::Ineq => return None,
                ArithOperator::Leq => {
                    let u = r / s;
                    builder.loop_(builder.allchar(), 0, u)
                }
                ArithOperator::Less => {
                    let u = r / s;
                    if r % s == 0 {
                        builder.loop_(builder.allchar(), 0, u - 1)
                    } else {
                        builder.loop_(builder.allchar(), 0, u)
                    }
                }
                ArithOperator::Geq => {
                    let l = r.div_ceil(s);
                    let lower = builder.pow(builder.allchar(), l);
                    builder.concat(smallvec![lower, builder.all()])
                }
                ArithOperator::Greater => {
                    let l = r.div_ceil(s);
                    let lower = builder.pow(builder.allchar(), l + 1);
                    builder.concat(smallvec![lower, builder.all()])
                }
            };
            return Some(RegularConstraint::new(x.clone(), re));
        }
    }
    None
}

pub trait InferringStrategy: Default + Clone {
    fn infer(&mut self) -> Option<Bounds>;
    fn conflict(&self) -> bool;
}
