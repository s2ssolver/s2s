//! An eager SMT solver for the theory of strings.
//! The solver reduces input problems over the theory of strings into a series SAT problems and solves them using a SAT solver.
//!
//! The solver bounds the length of strings in the input problem and encodes the problem into a SAT problem.
//! Whenever a SAT problem is satisfiable, the solver uses the result (propositional assigniment) to construct a model for the original problem.
//! If a SAT problem is unsatisfiable, the solver constructs a new SAT problem with relaxed variable bounds and tries again.
//! The solver terminates when a model is found or when the bounds are relaxed to the point where the problem is unsatisfiable.
//! Note however, that the solver does not guarantee that unsatisfiability is detected and thus might not terminate.

mod bounds;
mod encode;
pub mod model;
mod parse;
mod preprocess;
mod sat;
mod solver;

pub use parse::Parser;
pub use preprocess::{preprocess, PreprocessingResult};
pub use solver::{ConjunctiveSolver, Solver, SolverResult};
