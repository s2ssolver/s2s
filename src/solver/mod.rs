use core::panic;
use std::time::Instant;

use encoder::ProblemEncoder;

use itertools::Itertools;

pub use options::SolverOptions;

use crate::{
    abstraction::{build_abstraction, Abstraction},
    alphabet::{self, Alphabet},
    bounds::{infer::BoundInferer, Bounds, Interval},
    canonical::{Assignment, Formula},
    node::{Node, NodeKind, NodeManager, NodeSubstitution, Sorted},
    sat::to_cnf,
};

use crate::error::PublicError as Error;

//mod analysis;
mod encoder;

mod options;
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
            let v_bounds = bounds.get(var.as_ref());
            let lower = if let Some(lower) = v_bounds.and_then(|b| b.lower_finite()) {
                lower
            } else {
                0
            };
            let upper = if let Some(upper) = v_bounds.and_then(|b| b.upper_finite()) {
                upper.min(self.options.init_upper_bound)
            } else {
                self.options.init_upper_bound
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
        mngr: &mut NodeManager,
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
        let mut encoder = ProblemEncoder::new(alphabet, fm.vars());

        // Initialize the bounds
        let mut bounds = init_bounds;

        let mut round = 0;

        // Start Solving Loop
        loop {
            round += 1;
            log::info!("Round {} with bounds {}", round, bounds);
            // Encode and Solve
            t = Instant::now();
            let encoding = encoder.encode(&defs, &bounds, mngr)?;
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

                    if self.options.check_model && !self.check_assignment(fm, &assign) {
                        // If the assignment is not a solution, we found a bug.
                        panic!("The found model is invalid");
                    }
                    // encoder.print_debug(&cadical);
                    let subs = NodeSubstitution::from_assignment(&assign, mngr);
                    return Ok(SolverResult::Sat(Some(subs)));
                }

                Some(false) => {
                    log::info!("Unsat");
                    let failed = encoder.get_failed_literals(&cadical);
                    log::info!("{} Failed literal(s)", failed.len());
                    log::debug!("Failed literals: {}", failed.iter().join(", "));
                    // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                    match refine::refine_bounds(&failed, &bounds, fm, self.options.step, mngr) {
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
                            return Ok(SolverResult::Unsat);
                        }
                    }
                }
                None => panic!("Cadical failed to solve"),
            }
        }
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Formula, assign: &Assignment) -> bool {
        assign.satisfies(fm)
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
