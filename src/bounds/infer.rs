mod linear;
mod regular;
use std::rc::Rc;

use indexmap::IndexSet;
use linear::LinearRefiner;
use regular::RegularBoundsInferer;

use crate::{
    canonical::{
        ArithOperator, AtomKind, LinearArithTerm, LinearConstraint, Literal, RegularConstraint,
        WordEquation,
    },
    context::{Sorted, Variable},
    node::NodeManager,
};

use super::{Bounds, Interval};

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
                }
            }
            AtomKind::FactorConstraint(refc) => {
                self.in_re_vars.insert(refc.lhs().clone());
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

    pub fn add_literal(&mut self, lit: Literal, mngr: &mut NodeManager) {
        self.literals.insert(lit.clone());

        self.conflict |= self.literals.contains(&lit.inverted());

        // skip this if there is a conflict
        let pol = lit.polarity();
        match lit.atom().kind() {
            AtomKind::Boolvar(_) => (),
            AtomKind::InRe(reg) => self.add_reg(reg, pol, mngr),
            AtomKind::WordEquation(weq) => self.add_weq(weq, pol, mngr),
            AtomKind::FactorConstraint(_fac) => {
                todo!()
            }
            AtomKind::Linear(lc) => self.add_linear_constraint(lc),
        }
        self.fragment.and(&lit);
    }

    /// Returns true if the literals contain a conflict, i.e., a literal and its negation.
    pub fn conflicting(&self) -> bool {
        self.conflict || self.reg.conflict() || self.lin.conflict()
    }

    /// Infers the bounds of the variables in the literals.
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
                        if let Some(max) = nfa.longest() {
                            // This is none if the nfa contains cycles
                            // Add "|v| <= max" to the bounds
                            let lhs = LinearArithTerm::from_var(v.clone());
                            let lc = LinearConstraint::new(lhs, ArithOperator::Leq, max as i64);
                            self.lin.add_linear(lc);
                        }
                        if let Some(min) = nfa.shortest() {
                            // Add "|v| >= max" to the bounds
                            let lhs = LinearArithTerm::from_var(v.clone());
                            let lc = LinearConstraint::new(lhs, ArithOperator::Geq, min as i64);
                            self.lin.add_linear(lc);
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
            if bounds.get(&v).is_none() {
                if v.sort().is_string() {
                    bounds.set(v.as_ref().clone(), Interval::bounded_below(0));
                } else {
                    bounds.set(v.as_ref().clone(), Interval::unbounded());
                }
            }
        }
    }
}

trait InferringStrategy: Default + Clone {
    fn infer(&mut self) -> Option<Bounds>;
    fn conflict(&self) -> bool;
}
