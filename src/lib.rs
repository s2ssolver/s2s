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
// pub mod model;
// mod parse;
mod context;
mod preprocess;
mod repr;
mod sat;
mod solver;

use std::time::Instant;

use error::PublicError as Error;
use instance::Instance;

pub use solver::{get_solver, Solver, SolverResult};

pub fn solve(instance: &mut Instance) -> Result<SolverResult, Error> {
    // Preprocess the formula

    log::trace!("Solving formula {}", instance.get_script());
    let fm_original = instance.get_script().clone();
    let ts = Instant::now();

    // let mut subs = Substitution::new();

    // if instance.preprocess() {
    //     match preprocess(instance) {
    //         (PreprocessingResult::Unchanged(_), s) => {
    //             assert!(s.is_empty());
    //             log::debug!("No preprocessing applied.");
    //         }
    //         (PreprocessingResult::Changed(c), s) => {
    //             subs = s;
    //             instance.set_formula(c.into())
    //         }
    //     }
    //     log::info!("Preprocessing done ({}ms).", ts.elapsed().as_millis());
    // }
    log::debug!("Solving formula {}", instance.get_script());

    // Check if the formula is trivial
    // match instance.get_script().eval(&Substitution::defaults()) {
    //     Some(true) => {
    //         log::info!("Formula is trivially true");
    //         subs.use_defaults();
    //         return Ok(SolverResult::Sat(Some(subs)));
    //     }
    //     _ => (),
    // }
    // match instance.get_script().eval(&Substitution::new()) {
    //     Some(false) => {
    //         log::info!("Formula is trivially false");
    //         return Ok(SolverResult::Unsat);
    //     }
    //     _ => (),
    // }
    // check if the formula is trivially false
    // match fm_original.eval(&subs) {
    //     Some(false) => {
    //         log::info!("Formula is trivially false");
    //         return Ok(SolverResult::Unsat);
    //     }
    //     _ => (),
    // }

    if instance.dry_run() {
        log::info!("Dry run, terminating.");
        return Ok(SolverResult::Unknown);
    }

    // not trivally satifable or unsatisfiable
    let mut solver = get_solver(instance.clone())?;

    match solver.solve()? {
        SolverResult::Sat(Some(m)) => {
            let mut model = subs.compose(&m);
            model.use_defaults();
            Ok(SolverResult::Sat(Some(model)))
        }
        SolverResult::Sat(None) => Ok(SolverResult::Sat(None)),
        SolverResult::Unsat => Ok(SolverResult::Unsat),
        SolverResult::Unknown => Ok(SolverResult::Unknown),
    }
}
