use core::panic;

use encoder::ProblemEncoder;
use indexmap::IndexSet;
use itertools::Itertools;

use crate::{
    abstraction::{abstract_fm, Abstraction, Definition},
    bounds::Bounds,
    context::Context,
    preprocess::{self, PreprocessingError},
    repr::ir::{Formula, Literal, VarSubstitution},
    sat::to_cnf,
};

use crate::error::PublicError as Error;

//mod analysis;
mod encoder;
//mod engine;
//mod manager;

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

pub struct Solver<'a> {
    options: SolverOptions,
    context: &'a mut Context,
}

impl<'a> Solver<'a> {
    pub fn new(context: &'a mut Context) -> Self {
        Self {
            options: SolverOptions::default(),
            context,
        }
    }

    pub fn with_options(context: &'a mut Context, options: SolverOptions) -> Self {
        Self { options, context }
    }

    pub fn solve(&mut self, fm: &Formula, ctx: &Context) -> Result<SolverResult, Error> {
        // Preprocess
        let fm_preprocessed = self.preprocess(&fm)?;

        // Build the Boolean abstraction
        let abstraction = abstract_fm(&fm_preprocessed);

        // Initialize the bounds
        let init_bounds = self.init_bounds(&fm_preprocessed);

        // Initialize the alphabet
        let alphabet = self.init_alphabet(&fm_preprocessed);

        // Start CEGAR loop
        self.run(fm, abstraction, init_bounds, alphabet, ctx)
    }

    fn preprocess(&mut self, fm: &Formula) -> Result<Formula, PreprocessingError> {
        // TODO: Simplify
        preprocess::normalize(fm, self.context)
    }

    fn init_bounds(&self, fm: &Formula) -> Bounds {
        todo!("Initialize the bounds")
    }

    fn init_alphabet(&self, fm: &Formula) -> IndexSet<char> {
        todo!("Initialize the alphabet")
    }

    fn run(
        &mut self,
        fm: &Formula,
        abs: Abstraction,
        init_bounds: Bounds,
        alphabet: IndexSet<char>,
        ctx: &Context,
    ) -> Result<SolverResult, Error> {
        // INPUT: Instance (Abstraction(Definition, Skeleton), Init-Bounds, Alphabet, OriginalFormula)

        // Initialize the SAT solver
        let mut cadical: cadical::Solver = cadical::Solver::default();
        // Check if skeleton is trivially unsat
        let skeleton_cnf = to_cnf(abs.skeleton());
        for clause in skeleton_cnf.into_iter() {
            cadical.add_clause(clause);
        }
        if cadical.solve() == Some(false) {
            log::info!("Skeleton is unsat");
            return Ok(SolverResult::Unsat);
        }

        // Initialize the problem encoder

        // TODO: Filter defintions to only include supported literals
        let mut defs = abs.definitions().cloned().collect_vec();
        let mut encoder = ProblemEncoder::new(alphabet);

        // Initialize the bounds
        let mut bounds = init_bounds;

        // Start Solving Loop
        loop {
            // Encode and Solve
            let encoding = encoder.encode(&defs, &bounds, &ctx);
            let (cnf, asm) = encoding.into_inner();
            for clause in cnf {
                cadical.add_clause(clause);
            }

            match cadical.solve_with(asm.into_iter()) {
                Some(true) => {
                    // If SAT, check if model is a solution for the original formula.
                    let assign = encoder.get_model(&cadical).unwrap();
                    if self.check_assignment(fm, &assign) {
                        return Ok(SolverResult::Sat(Some(assign)));
                    } else {
                        let refined_defs = self.refine_abstraction(&defs, &assign, &abs);
                        if refined_defs.is_empty() {
                            encoder.block_assignment(&assign);
                        } else {
                            // Refine the abstraction
                            defs.extend(refined_defs);
                        }
                    }
                }
                Some(false) => {
                    let failed = encoder.get_failed_literals(&cadical);
                    // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                    match self.refine_bounds(&bounds, &failed) {
                        Some(new_bounds) => {
                            bounds = new_bounds;
                        }
                        None => return Ok(SolverResult::Unsat),
                    }
                }
                None => panic!("Cadical failed to solve"),
            }
        }
    }

    /// Refine the bounds based on the failed literals.
    /// Returns None if the upper bound of every variable is equal to or greater than the bounds of the smallest model any combination of the failed literals can produce.
    fn refine_bounds(&self, bounds: &Bounds, failed: &[Literal]) -> Option<Bounds> {
        todo!("Refine the bounds")
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Formula, assign: &VarSubstitution) -> bool {
        todo!("Check if the assignment is a solution for the formula")
    }

    /// Refines the abstraction by picking new definitions to encode.
    /// Returns the new definitions to encode.
    /// If the abstraction is already fully refined, returns an empty vector.
    fn refine_abstraction(
        &self,
        current_defs: &[Definition],
        assign: &VarSubstitution,
        abs: &Abstraction,
    ) -> Vec<Definition> {
        todo!("Refine the abstraction")
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
