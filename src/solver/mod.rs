use core::panic;
use std::time::Instant;

use encoder::ProblemEncoder;

use itertools::Itertools;

use crate::{
    abstraction::{build_abstraction, Abstraction},
    alphabet::{self, Alphabet},
    bounds::{infer::BoundInferer, step::BoundStep, Bounds, Interval},
    canonical::Formula,
    context::{Context, Sorted},
    node::{Node, NodeKind, NodeManager, NodeSubstitution},
    preprocess::{self, simp, PreprocessingError},
    sat::to_cnf,
};

use crate::error::PublicError as Error;

//mod analysis;
mod encoder;

mod preprocessing;
mod refine;
//mod engine;
//mod manager;

/// The result of a satisfiability check
pub enum SolverResult {
    /// The instance is satisfiable. The model, if given, is a solution to the instance.
    Sat(Option<NodeSubstitution>),
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
    pub fn get_model(&self) -> Option<&NodeSubstitution> {
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
const DEFAULT_UNSAT_ON_MAX_BOUND: bool = false;
#[derive(Debug, Clone)]
pub struct SolverOptions {
    dry: bool,
    simplify: bool,
    prep_passes: usize,
    cegar: bool,
    max_bounds: Option<Interval>,
    step: BoundStep,
    check_model: bool,
    unsat_on_max_bound: bool,
    init_upper_bound: i32,
    print_preprocessed: bool,
}
impl Default for SolverOptions {
    fn default() -> Self {
        Self {
            dry: false,
            simplify: DEFAULT_SIMPLIFY,
            prep_passes: DEFAULT_SIMP_MAX_STEPS,
            cegar: true,
            max_bounds: None,
            step: BoundStep::default(),
            check_model: DEFAULT_CHECK_MODEL,
            unsat_on_max_bound: DEFAULT_UNSAT_ON_MAX_BOUND,
            init_upper_bound: 2,
            print_preprocessed: false,
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
    /// If no solution is found within this bound, the solver returns `unknown`.
    /// Use `unsat_on_max_bound` to change this behavior to return `unsat` instead.
    pub fn max_bounds(&mut self, max_bounds: u32) -> &mut Self {
        self.max_bounds = Some(Interval::new(max_bounds, max_bounds));
        self
    }

    /// If a maximum bound is set (using [`max_bounds`](Self::max_bounds)), the solver will return `unsat` instead of `unknown` if the maximum bound is reached.
    pub fn unsat_on_max_bound(&mut self, unsat_on_max_bound: bool) -> &mut Self {
        self.unsat_on_max_bound = unsat_on_max_bound;
        self
    }

    /// The initial upper bound for the variables.
    /// This bounds is used to initialize the upper bounds for the variables for the first round of solving.
    pub fn init_upper_bound(&mut self, init_upper_bound: i32) -> &mut Self {
        self.init_upper_bound = init_upper_bound;
        self
    }

    /// Prints the preprocessed formula in SMT-LIB format.
    pub fn print_preprocessed(&mut self) -> &mut Self {
        self.print_preprocessed = true;
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

    pub fn solve(&mut self, root: &Node, mngr: &mut NodeManager) -> Result<SolverResult, Error> {
        log::info!("Starting solver");
        let mut timer = Instant::now();

        log::debug!("Solving: {}", root);

        // Preprocess
        let mut preprocessor = preprocessing::Preprocessor::default();
        let preprocessed = preprocessor.apply(root, self.options.prep_passes, mngr)?;
        log::info!("Preprocessed ({:?})", timer.elapsed());
        if self.options.print_preprocessed {
            //let smt = ir::smt::to_smtlib(&preprocessed);
            println!("{}", preprocessed.node());
        }

        // Early return if the formula is trivially sat/unsat
        if let NodeKind::Bool(v) = *preprocessed.node().kind() {
            return Ok(if v {
                SolverResult::Sat(Some(preprocessor.applied_subsitutions().clone()))
            } else {
                SolverResult::Unsat
            });
        }

        // Initialize the bounds
        timer = Instant::now();
        let init_bounds = match self.init_bounds(&preprocessed, mngr) {
            Some(bs) => bs,
            None => {
                log::info!("No valid initial bounds. Unsat.");
                return Ok(SolverResult::Unsat);
            }
        };

        timer = Instant::now();
        let abstraction = build_abstraction(&preprocessed)?;
        log::info!("Built abstraction ({:?})", timer.elapsed());

        log::info!("Initialized bounds ({:?})", timer.elapsed());
        log::debug!("Initial bounds: {}", init_bounds);
        todo!()
        // timer = Instant::now();

        // Initialize the alphabet
        let alphabet = alphabet::infer(&preprocessed);
        log::info!("Inferred alphabet ({:?})", timer.elapsed());
        log::debug!("Alphabet: {}", alphabet);
        timer = Instant::now();

        if self.options.dry {
        return Ok(SolverResult::Unknown);
        }
// Start CEGAR loop
        let res = self.run(&preprocessed, abstraction, init_bounds, alphabet, mngr);

        log::info!("Done solving ({:?})", timer.elapsed());
        res
    }

    // pub fn solve_old(&mut self, fm: &Formula, ctx: &mut Context) -> Result<SolverResult, Error> {
    //     log::info!("Starting solver");
    //     let mut timer = Instant::now();

    //     log::debug!("Solving: {}", fm);

    //     // Preprocess
    //     let (fm_preprocessed, applied_subst) = self.preprocess(fm.clone(), ctx)?;
    //     log::info!("Preprocessed ({:?})", timer.elapsed());
    //     log::debug!("Preprocessed formula: {}", fm_preprocessed);
    //     if self.options.print_preprocessed {
    //         let smt = ir::smt::to_smtlib(&fm_preprocessed);
    //         println!("{}", smt);
    //     }

    //     // Early return if the formula is trivially sat/unsat
    //     if fm_preprocessed == Formula::True {
    //         return Ok(SolverResult::Sat(Some(applied_subst)));
    //     } else if fm_preprocessed == Formula::False {
    //         return Ok(SolverResult::Unsat);
    //     }

    //     timer = Instant::now();

    //     // Build the Boolean abstraction
    //     let abstraction = abstract_fm(&fm_preprocessed);
    //     log::info!("Built abstraction ({:?})", timer.elapsed());
    //     timer = Instant::now();

    //     // Initialize the bounds
    //     let init_bounds = match self.init_bounds(&fm_preprocessed, ctx) {
    //         Some(bs) => bs,
    //         None => {
    //             log::info!("No valid initial bounds. Unsat.");
    //             return Ok(SolverResult::Unsat);
    //         }
    //     };
    //     log::info!("Initialized bounds ({:?})", timer.elapsed());
    //     log::debug!("Initial bounds: {}", init_bounds);

    //     timer = Instant::now();

    //     // Initialize the alphabet
    //     let alphabet = alphabet::infer(&fm_preprocessed);
    //     log::info!("Inferred alphabet ({:?})", timer.elapsed());
    //     log::debug!("Alphabet: {}", alphabet);
    //     timer = Instant::now();

    //     if self.options.dry {
    //         return Ok(SolverResult::Unknown);
    //     }
    //     // Start CEGAR loop
    //     let res = self.run(&fm_preprocessed, abstraction, init_bounds, alphabet, ctx);

    //     log::info!("Done solving ({:?})", timer.elapsed());
    //     res
    // }

    fn init_bounds(&self, fm: &Formula, mngr: &mut NodeManager) -> Option<Bounds> {
        let mut inferer = BoundInferer::default();
        for lit in fm.entailed_lits() {
            inferer.add_literal(lit.clone(), mngr)
        }

        let mut bounds = inferer.infer()?;
        log::debug!("Inferred bounds for entailed literals: {}", bounds);
        for var in fm
            .vars()
            .iter()
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
                upper.min(self.options.init_upper_bound as i32)
            } else {
                self.options.init_upper_bound as i32
            }
            .max(lower)
            .max(1); // need to be at least 1
            bounds.set(var.as_ref().clone(), Interval::new(lower, upper));
        }
        let clamped = self.clamp_bounds(bounds);
        // Clamp the bounds to the maximum bounds, if set
        Some(clamped)
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

        let defs = abs.definitions().cloned().collect_vec();
        let mut encoder = ProblemEncoder::new(alphabet);

        // Initialize the bounds
        let mut bounds = init_bounds;

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
                    // encoder.print_debug(&cadical);
                    return Ok(SolverResult::Sat(Some(assign)));
                }

                Some(false) => {
                    log::info!("Unsat");
                    let failed = encoder.get_failed_literals(&cadical);
                    log::info!("{} Failed literal(s)", failed.len());
                    log::debug!("Failed literals: {}", failed.iter().join(", "));
                    // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                    match refine::refine_bounds(&failed, &bounds, fm, self.options.step, ctx) {
                        refine::BoundRefinement::Refined(b) => {
                            let clamped = self.clamp_bounds(b);
                            // if the clamped bound are equal to the bounds we used in this round, nothing changed
                            // in that case, the limit is reached
                            if clamped == bounds {
                                if self.options.unsat_on_max_bound {
                                    return Ok(SolverResult::Unsat);
                                } else {
                                    return Ok(SolverResult::Unknown);
                                }
                            } else {
                                bounds = clamped;
                            }
                        }
                        refine::BoundRefinement::SmallModelReached => {
                            // If we blocked an assignment, we can't be sure that the formula is unsat.
                            // Otherwise, we can return UNSAT.
                            if _blocked_assignments > 0 {
                                return Ok(SolverResult::Unknown);
                            } else {
                                return Ok(SolverResult::Unsat);
                            }
                        }
                    }
                }
                None => panic!("Cadical failed to solve"),
            }
        }
        todo!()
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Formula, assign: &NodeSubstitution, ctx: &mut Context) -> bool {
        // let applied = assign.apply(fm.clone(), ctx);
        // let reduced = applied.reduce();

        // matches!(reduced, Formula::True)
        todo!()
    }

    /// Refines the abstraction by picking new definitions to encode.

    /// Clamp the bounds to the maximum bounds.
    fn clamp_bounds(&self, bounds: Bounds) -> Bounds {
        if let Some(max_bound) = self.options.max_bounds {
            let mut new_bounds = bounds.clone();
            for (var, bound) in bounds.iter() {
                let new_bound = bound.intersect(max_bound);
                new_bounds.set(var.clone(), new_bound);
            }
            new_bounds
        } else {
            bounds
        }
    }
}
