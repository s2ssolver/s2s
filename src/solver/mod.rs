use core::panic;
use std::time::Instant;

use encoder::ProblemEncoder;

use itertools::Itertools;

use crate::{
    abstraction::{abstract_fm, Abstraction, Definition},
    alphabet::{self, Alphabet},
    bounds::{infer::BoundInferer, step::BoundStep, Bounds, Interval},
    context::{Context, Sorted},
    ir::{Formula, VarSubstitution},
    preprocess::{self, simp, PreprocessingError},
    sat::to_cnf,
};

use crate::error::PublicError as Error;

//mod analysis;
mod encoder;
mod refine;
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

const DEFAULT_SIMPLIFY: bool = true;
const DEFAULT_SIMP_MAX_STEPS: usize = 500;
const DEFAULT_CHECK_MODEL: bool = false;
#[derive(Debug, Clone)]
pub struct SolverOptions {
    dry: bool,
    simplify: bool,
    simp_iters: usize,
    cegar: bool,
    max_bounds: usize,
    step: BoundStep,
    check_model: bool,
}
impl Default for SolverOptions {
    fn default() -> Self {
        Self {
            dry: false,
            simplify: DEFAULT_SIMPLIFY,
            simp_iters: DEFAULT_SIMP_MAX_STEPS,
            cegar: true,
            max_bounds: usize::MAX,
            step: BoundStep::default(),
            check_model: DEFAULT_CHECK_MODEL,
        }
    }
}

impl SolverOptions {
    /// Whether to use a dry-run mode.
    /// In dry-run mode, the solver does not actually solve the instance, but only preprocesses it.
    /// If after preprcessing the formula is not trivially sat/unsat, the solver returns `Unknown`.
    pub fn dry(&mut self, dry: bool) -> &mut Self {
        self.dry = dry;
        self
    }

    /// Whether to simplify the formula before solving it.
    /// Simplification is done by applying algebraic simplifications to the formula.
    pub fn simplify(&mut self, simplify: bool) -> &mut Self {
        self.simplify = simplify;
        self
    }

    /// Whether to use a counterexample-guided abstraction refinement (CEGAR) strategy if unsupported literals are found.
    ///
    /// If CEGAR is enabled, the solver solves an abstracted version of the formula containing only supported literals.
    /// If the abstracted formula is satisfiable, the solver checks if the model is a solution to the original formula.
    /// If the model is not a solution, the solver tries to refine the abstraction and solve the abstracted formula again.
    /// If the abstracted formula is unsatisfiable, the solver refines the abstraction and tries again.
    /// If this is set to false, the solver will refuse to solve the formula if it contains unsupported literals.
    pub fn cegar(&mut self, cegar: bool) -> &mut Self {
        self.cegar = cegar;
        self
    }

    /// The maximum upper bound the solver will try to find a solution for.
    /// If no solution is found within this bound, the solver returns `Unknown`.
    pub fn max_bounds(&mut self, max_bounds: usize) -> &mut Self {
        self.max_bounds = max_bounds;
        self
    }
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

    pub fn solve(&mut self, fm: &Formula, ctx: &mut Context) -> Result<SolverResult, Error> {
        log::info!("Starting solver");
        let mut timer = Instant::now();

        log::debug!("Solving: {}", fm);

        // Preprocess
        let (fm_preprocessed, applied_subst) = self.preprocess(fm.clone(), ctx)?;
        log::info!("Preprocessed ({:?})", timer.elapsed());
        log::debug!("Preprocessed formula: {}", fm_preprocessed);

        // Early return if the formula is trivially sat/unsat
        if fm_preprocessed == Formula::True {
            return Ok(SolverResult::Sat(Some(applied_subst)));
        } else if fm_preprocessed == Formula::False {
            return Ok(SolverResult::Unsat);
        }

        timer = Instant::now();

        // Build the Boolean abstraction
        let abstraction = abstract_fm(&fm_preprocessed);
        log::info!("Built abstraction ({:?})", timer.elapsed());
        timer = Instant::now();

        // Initialize the bounds
        let init_bounds = match self.init_bounds(&fm_preprocessed, ctx) {
            Some(bs) => bs,
            None => {
                log::info!("No valid initial bounds. Unsat.");
                return Ok(SolverResult::Unsat);
            }
        };
        log::info!("Initialized bounds ({:?})", timer.elapsed());
        log::debug!("Initial bounds: {}", init_bounds);

        timer = Instant::now();

        // Initialize the alphabet
        let alphabet = alphabet::infer(&fm_preprocessed);
        log::info!("Inferred alphabet ({:?})", timer.elapsed());
        log::debug!("Alphabet: {}", alphabet);
        timer = Instant::now();

        if self.options.dry {
            return Ok(SolverResult::Unknown);
        }
        // Start CEGAR loop
        let res = self.run(&fm_preprocessed, abstraction, init_bounds, alphabet, ctx);

        log::info!("Done solving ({:?})", timer.elapsed());
        res
    }

    fn preprocess(
        &mut self,
        fm: Formula,
        ctx: &mut Context,
    ) -> Result<(Formula, VarSubstitution), PreprocessingError> {
        let t = Instant::now();
        let (fm, subst) = if self.options.simplify {
            let simped = simp::simplify(fm.clone(), ctx, self.options.simp_iters);
            (simped.formula, simped.subst)
        } else {
            (fm.clone(), VarSubstitution::default())
        };
        log::info!("Simplified formula ({:?})", t.elapsed());

        Ok((preprocess::normalize(fm, ctx)?, subst))
    }

    fn init_bounds(&self, fm: &Formula, ctx: &mut Context) -> Option<Bounds> {
        let mut inferer = BoundInferer::default();
        for lit in fm.entailed_literals() {
            inferer.add_literal(lit.clone(), ctx)
        }

        let mut bounds = inferer.infer()?;
        log::debug!("Inferred bounds for entailed literals: {}", bounds);
        for var in ctx
            .vars()
            .filter(|v| v.sort().is_int() || v.sort().is_string())
        {
            // TODO: Check options for initial min/max bounds
            let v_bounds = bounds.get(var.as_ref());
            let lower = if let Some(lower) = v_bounds.and_then(|b| b.lower_finite()) {
                lower
            } else {
                0.into()
            };
            let upper = if let Some(upper) = v_bounds.and_then(|b| b.upper_finite()) {
                upper.min(2)
            } else {
                2
            }
            .max(lower)
            .max(1); // need to be at least 1
            bounds.set(var.as_ref().clone(), Interval::new(lower, upper));
        }
        Some(bounds)
    }

    fn run(
        &mut self,
        fm: &Formula,
        abs: Abstraction,
        init_bounds: Bounds,
        alphabet: Alphabet,
        ctx: &mut Context,
    ) -> Result<SolverResult, Error> {
        // INPUT: Instance (Abstraction(Definition, Skeleton), Init-Bounds, Alphabet, OriginalFormula)

        // Initialize the SAT solver
        let mut cadical: cadical::Solver = cadical::Solver::default();
        // Check if skeleton is trivially unsat
        let skeleton_cnf = to_cnf(abs.skeleton());

        let mut t = Instant::now();
        for clause in skeleton_cnf.into_iter() {
            cadical.add_clause(clause);
        }
        if cadical.solve() == Some(false) {
            log::info!("Skeleton is unsat");
            return Ok(SolverResult::Unsat);
        }
        log::info!("Skeleton is SAT ({:?})", t.elapsed());

        // Initialize the problem encoder

        // TODO: Filter defintions to only include supported literals
        let mut defs = abs.definitions().cloned().collect_vec();
        let mut encoder = ProblemEncoder::new(alphabet);

        // Initialize the bounds
        let mut bounds = init_bounds;

        let mut _blocked_assignments = 0;
        let mut round = 0;

        // Start Solving Loop
        loop {
            round += 1;
            log::info!("Round {} with bounds {}", round, bounds);
            // Encode and Solve
            t = Instant::now();
            let encoding = encoder.encode(&defs, &bounds, ctx)?;
            let (cnf, asm) = encoding.into_inner();
            log::info!("Encoded ({} clauses) ({:?})", cnf.len(), t.elapsed());
            t = Instant::now();
            for clause in cnf {
                cadical.add_clause(clause);
            }
            log::info!("Added clauses to cadical ({:?})", t.elapsed());

            t = Instant::now();
            let res = cadical.solve_with(asm.into_iter());
            log::info!("Done SAT solving: {:?} ({:?})", res, t.elapsed());

            match res {
                Some(true) => {
                    // If SAT, check if model is a solution for the original formula.
                    let assign = encoder.get_model(&cadical);
                    log::info!("Found model: {}", assign);

                    if self.options.check_model && !self.check_assignment(fm, &assign, ctx) {
                        // If the assignment is not a solution, we found a bug.
                        panic!("The found model is invalid");
                    }
                    //                    encoder.print_debug(&cadical);
                    return Ok(SolverResult::Sat(Some(assign)));
                }

                Some(false) => {
                    log::info!("Unsat");
                    let failed = encoder.get_failed_literals(&cadical);
                    log::info!("{} Failed literal(s)", failed.len());
                    log::debug!("Failed literals: {}", failed.iter().join(", "));
                    // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                    match refine::refine_bounds(&failed, &bounds, fm, self.options.step, ctx) {
                        refine::BoundRefinement::Refined(b) => bounds = b,
                        refine::BoundRefinement::SmallModelReached => {
                            // If we blocked an assignment, we can't be sure that the formula is unsat.
                            // Otherwise, we can return UNSAT.
                            if _blocked_assignments > 0 {
                                return Ok(SolverResult::Unknown);
                            } else {
                                return Ok(SolverResult::Unsat);
                            }
                        }
                        refine::BoundRefinement::LimitReached => {
                            // TODO: specify in the options what should be returned here
                            return Ok(SolverResult::Unknown);
                        }
                    }
                }
                None => panic!("Cadical failed to solve"),
            }
        }
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Formula, assign: &VarSubstitution, ctx: &mut Context) -> bool {
        let applied = assign.apply(fm.clone(), ctx);
        let reduced = applied.reduce();

        matches!(reduced, Formula::True)
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
