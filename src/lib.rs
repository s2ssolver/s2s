use std::collections::HashSet;

use encode::{
    equations::WoorpjeEncoder, EncodingResult, PredicateEncoder, VariableBounds,
    WordEquationEncoder,
};
use formula::{Atom, Formula, Predicate};
use model::{words::WordEquation, Variable};

use crate::encode::substitution::SubstitutionEncoder;

mod encode;
mod formula;
mod model;
pub mod parse;
mod sat;

/// A problem instance, consisting of a formula and a set of variables
/// Should be created using the `parse` module
pub struct Instance {
    /// The formula to solve
    formula: Formula,
    /// The set of all variables
    vars: HashSet<Variable>,
    /// The maximum bound for any variable to check.
    /// If `None`, no bound is set, which will might in an infinite search if the instance is not satisfiable.
    /// If `Some(n)`, the solver will only check for a solution with a bound of `n`.
    /// If no solution is found with every variable bound to `n`, the solver will return `Unsat`.
    ubound: Option<usize>,
}

impl Instance {
    pub fn set_bound(&mut self, bound: usize) {
        self.ubound = Some(bound);
    }

    pub fn remove_bound(&mut self) {
        self.ubound = None;
    }

    pub fn get_formula(&self) -> &Formula {
        &self.formula
    }

    pub fn get_vars(&self) -> &HashSet<Variable> {
        &self.vars
    }
}

/// The result of a satisfiability check
pub enum SolverResult {
    /// The instance is satisfiable
    Sat,
    /// The instance is unsatisfiable
    Unsat,
    /// The solver could not determine the satisfiability of the instance
    Unknown,
}

impl SolverResult {
    /// Returns true if the instance is satisfiable
    pub fn is_sat(&self) -> bool {
        match self {
            SolverResult::Sat => true,
            _ => false,
        }
    }

    /// Returns true if the instance is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        match self {
            SolverResult::Unsat => true,
            _ => false,
        }
    }
}

/// A solver for a problem instance.
/// A solver provides a `solve` method that takes an instance and decides whether it is satisfiable.
/// Implementations of this trait accept different kinds of instances.
// todo: Default solver for formulas.
pub trait Solver {
    /// Solve the given instance.
    fn solve(&mut self) -> SolverResult;
}

/// The Woorpje solver for word equations.
/// This solver uses a SAT solver to check whether a word equation is satisfiable.
/// Can only solver instances with a single word equation.
pub struct Woorpje {
    equation: WordEquation,
    bounds: VariableBounds,
    max_bound: Option<usize>,
}

impl Woorpje {
    /// Create a new Woorpje solver for the given instance.
    /// Returns an error if the instance is not a single word equation.
    pub fn new(instance: &Instance) -> Result<Self, String> {
        if let Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) = &instance.formula {
            Ok(Self {
                equation: eq.clone(),
                bounds: VariableBounds::new(1),
                max_bound: instance.ubound,
            })
        } else {
            Err("Instance is not a single word equation".to_string())
        }
    }
}

impl Woorpje {
    fn encode_bounded(&self) -> EncodingResult {
        let mut encoding = EncodingResult::empty();
        let mut subs_encoder =
            SubstitutionEncoder::new(self.equation.alphabet(), self.equation.variables());

        let subs_cnf = subs_encoder.encode(&self.bounds);
        encoding.join(subs_cnf);

        let mut encoder = WoorpjeEncoder::new(self.equation.clone());
        encoding.join(encoder.encode(&self.bounds, subs_encoder.get_encoding()));
        encoding
    }
}

impl Solver for Woorpje {
    fn solve(&mut self) -> SolverResult {
        while self.bounds.double(self.max_bound) {
            log::info!("Solving {} with bounds {}", self.equation, self.bounds);
            let encoding = self.encode_bounded();
            match encoding {
                EncodingResult::Cnf(clauses) => {
                    let mut cadical: cadical::Solver = cadical::Solver::new();
                    for clause in clauses.into_iter() {
                        cadical.add_clause(clause);
                    }
                    if let Some(true) = cadical.solve() {
                        return SolverResult::Sat;
                    }
                }
                EncodingResult::Trivial(false) => return SolverResult::Unsat,
                EncodingResult::Trivial(true) => return SolverResult::Sat,
            }
        }
        SolverResult::Unknown
    }
}
