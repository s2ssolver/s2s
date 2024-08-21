use crate::repr::ir::{Formula, VarSubstitution};

use self::engine::AbstractionSolver;

mod analysis;
mod engine;

mod manager;

/// The result of a satisfiability check
pub enum SolverResult {
    /// The instance is satisfiable. The model, if given, is a solution to the instance.
    Sat(Option<VarSubstitution>),
    /// The instance is unsatisfiable
    Unsat,
    /// The solver could not determine the satisfiability of the instance
    Unknown,
}

impl SolverResult {
    /// Returns true if the instance is satisfiable
    pub fn is_sat(&self) -> bool {
        matches!(self, SolverResult::Sat(_))
    }

    /// Returns the model if the instance is satisfiable
    pub fn get_model(&self) -> Option<&VarSubstitution> {
        match self {
            SolverResult::Sat(model) => model.as_ref(),
            _ => None,
        }
    }

    /// Returns true if the instance is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        matches!(self, SolverResult::Unsat)
    }
}

impl std::fmt::Display for SolverResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverResult::Sat(_) => write!(f, "sat"),
            SolverResult::Unsat => write!(f, "unsat"),
            SolverResult::Unknown => write!(f, "unknown"),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SolverOptions {
    /// Whether to use a dry-run mode.
    /// In dry-run mode, the solver does not actually solve the instance, but only preprocesses it.
    /// If after preprcessing the formula is not trivially sat/unsat, the solver returns `Unknown`.
    dry: bool,

    /// Whether to simplify the formula before solving it.
    /// Simplification is done by applying algebraic simplifications to the formula.
    simplify: bool,

    /// Whether to use a counterexample-guided abstraction refinement (CEGAR) strategy if unsupported literals are found.
    /// If CEGAR is enabled, the solver solves an abstracted version of the formula containing only supported literals.
    /// If the abstracted formula is satisfiable, the solver checks if the model is a solution to the original formula.
    /// If the model is not a solution, the solver tries to refine the abstraction and solve the abstracted formula again.
    /// If the abstracted formula is unsatisfiable, the solver refines the abstraction and tries again.
    /// If this is set to false, the solver will refuse to solve the formula if it contains unsupported literals.
    cegar: bool,

    /// The maximum upper bound the solver will try to find a solution for.
    /// If no solution is found within this bound, the solver returns `Unknown`.
    max_bounds: usize,
}

/// The solver.
#[derive(Default)]
pub struct Solver {
    options: SolverOptions,
}

impl Solver {
    pub fn with_options(options: SolverOptions) -> Self {
        Self { options }
    }

    pub fn solve(&self, fm: Formula) -> SolverResult {
        // Preprocess:
        let fm_preprocessed = self.preprocess(&fm);

        // Build the Boolean abstraction

        // Initialize the bounds

        // Initialize the alphabet

        // Start CEGAR loop

        // Start Solving Loop
        // Encode and Solve
        // If SAT, check if model is solution. If not, refine the abstraction and repeat.
        // If UNSAT: Bound Refinement
        // IF bounds are at max, return UNSAT

        SolverResult::Unknown
    }

    pub fn preprocess(&self, fm: &Formula) -> Formula {
        // Simplify
        // Normal-Form
        // Cegar-Abstraction
    }
}

/// A solver for a problem instance.
/// A solver provides a `solve` method that takes an instance and decides whether it is satisfiable.
/// Implementations of this trait accept different kinds of instances.
// todo: Default solver for formulas.
pub trait SolverOld {
    /// Solve the given instance.
    fn solve(&mut self) -> Result<SolverResult, Error>;
}

/// Returns a solver for the given instance.
pub fn get_solver(inst: Instance) -> Result<Box<dyn SolverOld>, Error> {
    AbstractionSolver::new(inst).map(|s| Box::new(s) as Box<dyn SolverOld>)
}
