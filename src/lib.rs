//! An eager SMT solver for the theory of strings.
//! The solver reduces input problems over the theory of strings into a series SAT problems and solves them using a SAT solver.
//!
//! The solver bounds the length of strings in the input problem and encodes the problem into a SAT problem.
//! Whenever a SAT problem is satisfiable, the solver uses the result (propositional assigniment) to construct a model for the original problem.
//! If a SAT problem is unsatisfiable, the solver constructs a new SAT problem with relaxed variable bounds and tries again.
//! The solver terminates when a model is found or when the bounds are relaxed to the point where the problem is unsatisfiable.
//! Note however, that the solver does not guarantee that unsatisfiability is detected and thus might not terminate.

#![allow(clippy::comparison_chain)]

mod abstraction;
mod alphabet;
mod bounds;
mod domain;
mod interval;

mod encode;
mod error;

mod engine;
pub mod node;
mod preprocess;
mod sat;

pub mod smt;
mod solver;

use std::{io::BufRead, time::Instant};

pub use error::PublicError as Error;

pub use engine::Engine as Blastr;
use node::NodeManager;
use smt::{Interpreter, Script, ScriptBuilder};
pub use solver::{SolverAnswer, SolverOptions};

/// Solves an SMT problem over the theory of strings.
/// The input problem must be in SMT-LIB format.
/// Returns the result of the satisfiability check.
/// Optionally, the solver can be configured with additional options.
/// If no options are given, the solver uses the default options.
pub fn solve_smt(smt: impl BufRead, options: Option<SolverOptions>) -> Result<(), Error> {
    let mut mngr = NodeManager::default();

    let t = Instant::now();
    // Parse the input problem
    let script = parse_script(smt, &mut mngr)?;
    log::info!("Parsed in {:?}", t.elapsed());

    let mut interpreter = Interpreter::new(options.unwrap_or_default(), &mut mngr);
    interpreter.run(&script)
}

pub fn parse_script(smt: impl BufRead, mngr: &mut NodeManager) -> Result<Script, Error> {
    let parser = ScriptBuilder::new(mngr);
    Ok(parser.parse_script(smt)?)
}
