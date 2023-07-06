//! An eager SMT solver for the theory of strings.
//! The solver reduces input problems over the theory of strings into a series SAT problems and solves them using a SAT solver.
//!
//! The solver bounds the length of strings in the input problem and encodes the problem into a SAT problem.
//! Whenever a SAT problem is satisfiable, the solver uses the result (propositional assigniment) to construct a model for the original problem.
//! If a SAT problem is unsatisfiable, the solver constructs a new SAT problem with relaxed variable bounds and tries again.
//! The solver terminates when a model is found or when the bounds are relaxed to the point where the problem is unsatisfiable.
//! Note however, that the solver does not guarantee that unsatisfiability is detected and thus might not terminate.

mod abstr;
mod bounds;
mod encode;
pub mod error;
mod instance;
pub mod model;
mod parse;
mod preprocess;
mod sat;
mod solver;

use std::time::Instant;

use error::Error;
use instance::Instance;
pub use parse::Parser;
pub use preprocess::{preprocess, PreprocessingResult};
pub use solver::{get_solver, Solver, SolverResult};

use crate::model::{Evaluable, Substitution};

pub fn solve(instance: &mut Instance) -> Result<SolverResult, Error> {
    // Preprocess the formula
    let ts = Instant::now();

    let mut subs = Substitution::new();
    match preprocess(instance) {
        (PreprocessingResult::Unchanged(_), s) => {
            assert!(s.is_empty());
            log::debug!("No preprocessing applied.");
        }
        (PreprocessingResult::Changed(c), s) => {
            subs = s;
            instance.set_formula(c)
        }
    }
    log::info!("Preprocessing done ({}ms).", ts.elapsed().as_millis());
    log::debug!("Formula post preprocessing: {}", instance.get_formula());

    // Check if the formula is trivial
    match instance.get_formula().eval(&subs) {
        Some(true) => {
            log::info!("Formula is trivially true");
            subs.use_defaults();
            return Ok(SolverResult::Sat(subs));
        }
        Some(false) => {
            log::info!("Formula is trivially false");
            return Ok(SolverResult::Unsat);
        }
        _ => (),
    }
    // not trivally satifable or unsatisfiable
    let mut solver = get_solver(instance.clone())?;

    match solver.solve()? {
        SolverResult::Sat(m) => {
            let mut model = subs.compose(&m);
            model.use_defaults();
            Ok(SolverResult::Sat(model))
        }
        SolverResult::Unsat => Ok(SolverResult::Unsat),
        SolverResult::Unknown => {
            log::warn!("Solver returned unknown");
            Ok(SolverResult::Unknown)
        }
    }
}
