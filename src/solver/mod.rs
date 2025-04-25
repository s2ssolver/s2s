use core::panic;
use std::{rc::Rc, time::Instant};

use crate::{
    ast::VarSubstitution,
    context::{Context, Sort},
    domain::Domain,
};
use encoder::DefintionEncoder;

use indexmap::IndexMap;
use itertools::Itertools;

pub use options::SolverOptions;
use refine::BoundRefiner;
use rustsat::types::Lit;
use rustsat::{
    encodings::CollectClauses,
    solvers::{Solve, SolveIncremental},
};
use rustsat_cadical::CaDiCaL;

use crate::{
    abstraction::LitDefinition,
    alphabet::Alphabet,
    ast::Node,
    sat::{to_cnf, PFormula},
};

use crate::error::PublicError as Error;

mod encoder;
mod options;
mod refine;

/// The result of a satisfiability check.
/// Can be either of
/// - `Sat` if the instance is satisfiable. The model, if given, is a solution to the instance.
/// - `Unsat` if the instance is unsatisfiable
/// - `Unknown` if the solver could not determine the satisfiability of the instance
#[derive(Debug, Clone)]
pub enum SolverAnswer {
    /// The instance is satisfiable. The model, if given, is a solution to the instance.
    Sat(Option<VarSubstitution>),
    /// The instance is unsatisfiable
    Unsat,
    /// The solver could not determine the satisfiability of the instance
    Unknown,
}

impl SolverAnswer {
    /// Returns true if the instance is satisfiable
    pub fn is_sat(&self) -> bool {
        matches!(self, SolverAnswer::Sat(_))
    }

    /// Returns the model if the instance is satisfiable
    pub fn get_model(&self) -> Option<&VarSubstitution> {
        match self {
            SolverAnswer::Sat(model) => model.as_ref(),
            _ => None,
        }
    }

    /// Returns true if the instance is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        matches!(self, SolverAnswer::Unsat)
    }
}

impl std::fmt::Display for SolverAnswer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverAnswer::Sat(_) => write!(f, "sat"),
            SolverAnswer::Unsat => write!(f, "unsat"),
            SolverAnswer::Unknown => write!(f, "unknown"),
        }
    }
}

/// The main solver.
/// Solves the given formula by iteratively refining the bounds of the variables until a solution is found or the bounds are exhausted.
/// In each iteration, the solver encodes the definitions of the variables and adds them to the SAT solver.
/// The SAT solver is then called to check the satisfiability of the formula.
/// If the formula is satisfiable, the solver decodes the propositional model to a first-order model and returns it.
/// If the formula is unsatisfiable, the solver refines the bounds of the variables and continues.
/// This is repeated until
///
/// - a solution is found
/// - the bounds exceed the bounds of a presumed smallest model, in that case `UNSAT` is returned
/// - the bounds are at the set maximum bounds, in that case either `UNSAT` or `UNKNOWN` is returned, based on the options
/// - the bounds are frozen and the solver cannot refine them anymore, in that case `UNKNOWN` is returned
///
/// After each call to `solve`, more definitions can be added to the solver.
/// The solver works incrementally, so adding definitions does not require a full restart.
pub(crate) struct Solver {
    options: SolverOptions,

    cadical: Box<CaDiCaL<'static, 'static>>,

    skeleton: PFormula,
    /// The definitions of the abstraction variables
    defs: IndexMap<Lit, LitDefinition>,

    encoder: DefintionEncoder,
    next_bounds: Domain,

    refiner: BoundRefiner,

    frozen_bounds: bool,
}

impl Solver {
    pub fn new(
        options: SolverOptions,
        skeleton: PFormula,
        alphabet: Rc<Alphabet>,
        init_bounds: Domain,
    ) -> Self {
        let mut sat_solver = rustsat_cadical::CaDiCaL::default();
        let cnf = to_cnf(&skeleton);
        sat_solver.add_cnf(cnf).unwrap();
        let refiner = BoundRefiner::default();
        Self {
            options,
            skeleton,
            cadical: Box::new(sat_solver),
            refiner,
            defs: IndexMap::new(),
            encoder: DefintionEncoder::new(alphabet),
            next_bounds: init_bounds,
            frozen_bounds: false,
        }
    }

    /// Adds a definition to the solver that will be encoded in the next call to `solve`.
    pub fn add_definition(&mut self, def: &LitDefinition) {
        if self.defs.contains_key(&def.defining()) {
            panic!(
                "Definition for literal {} already exists. Cannot redefine.",
                def.defining()
            );
        }
        self.defs.insert(def.defining(), def.clone());
    }

    /// Freezes the bounds. After this call, the bounds will not be refined anymore.
    /// Instead, every call to `solve` will use the the same bounds as the last call (or the initial bounds, if no call to `solve` has been made yet).
    /// Therefore, the call to `solve` will always return the same result, which is either SAT, or UNKNOWN.
    pub fn freeze_bounds(&mut self) {
        self.frozen_bounds = true;
    }

    /// Solve the formula with the current bounds.
    /// The function encodes all definitions that have been added to the solver, adds the clauses to the SAT solver, and calls the SAT solver.
    /// Returns the result of the satisfiability check.
    pub fn solve(&mut self, ctx: &mut Context) -> Result<SolverAnswer, Error> {
        // Initialize the bounds

        let mut round = 0;

        // Start Solving Loop
        loop {
            // keep track of the current bounds
            let bounds = self.next_bounds.clone();
            round += 1;
            log::info!("Round {} with bounds {}", round, bounds);

            // Encode and Solve
            let mut timer = Instant::now();

            let assumptions = self.encoder.encode(
                self.defs.values().cloned(),
                &bounds,
                self.cadical.as_mut(),
                ctx,
            )?;

            log::info!(
                "Encoded ({} clauses) ({:?})",
                self.cadical.n_clauses(),
                timer.elapsed()
            );
            timer = Instant::now();

            log::info!("Added clauses to cadical ({:?})", timer.elapsed());

            timer = Instant::now();

            let res = self.cadical.as_mut().solve_assumps(&assumptions);
            log::info!("Done SAT solving: {:?} ({:?})", res, timer.elapsed());

            match res {
                Ok(res) => match res {
                    rustsat::solvers::SolverResult::Sat => {
                        // If SAT, check if model is a solution for the original formula.
                        let subs = self.encoder.get_model(&self.cadical, ctx);
                        log::info!("Encoding is SAT");
                        //self.encoder.print_debug(&self.cadical);
                        return Ok(SolverAnswer::Sat(Some(subs)));
                    }
                    rustsat::solvers::SolverResult::Unsat => {
                        if self.frozen_bounds {
                            // Don't refine bounds if they are frozen, return UNKNOWN
                            return Ok(SolverAnswer::Unknown);
                        }
                        log::info!("Unsat");
                        let failed = self.encoder.get_failed_literals(&mut self.cadical);
                        log::info!("{} Failed literal(s)", failed.len());
                        log::debug!("Failed literals: {}", failed.iter().join(", "));
                        // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                        let fm = self
                            .to_formula(ctx, &self.skeleton)
                            .unwrap_or(ctx.ast().ttrue());
                        match self.refiner.refine_bounds(
                            &failed,
                            &bounds,
                            &fm,
                            self.options.step,
                            ctx,
                        ) {
                            refine::BoundRefinement::Refined(b) => {
                                let clamped = self.clamp_bounds_in_dom(b);
                                // if the clamped bound are equal to the bounds we used in this round, nothing changed
                                // in that case, the limit is reached
                                if clamped == bounds {
                                    if self.options.unsat_on_max_bound {
                                        return Ok(SolverAnswer::Unsat);
                                    } else {
                                        return Ok(SolverAnswer::Unknown);
                                    }
                                } else {
                                    self.next_bounds = clamped
                                }
                            }
                            refine::BoundRefinement::SmallModelReached => {
                                return Ok(SolverAnswer::Unsat);
                            }
                        }
                    }
                    rustsat::solvers::SolverResult::Interrupted => {
                        log::error!("Cadical was interrupted");
                        return Ok(SolverAnswer::Unknown);
                    }
                },
                Err(e) => {
                    log::error!("Cadical failed to solve: {e}");
                    return Ok(SolverAnswer::Unknown);
                }
            }
        }
    }

    /// Blocks an assignment by adding a clause to the SAT solver that excludes the assignment.
    /// This block all assignments for each variable indepenently, not the assignment as a whole.
    /// That is, if the assignment is `x -> abc` and `y -> def`, the both "x = abc" and "y = def" are blocked for every solution.
    pub fn block(&mut self, asn: &VarSubstitution) {
        let (clauses, _) = self.encoder.block_assignment(asn).into_inner();
        self.cadical.add_cnf(clauses).unwrap();
    }

    /// Makes sure the bounds in the domain do not exceed the maximum bounds set in the options.
    fn clamp_bounds_in_dom(&self, dom: Domain) -> Domain {
        let mut new_dom = dom.clone();
        for (var, bound) in dom.iter_string() {
            let new_bound = bound.intersect(self.options.max_bounds);
            new_dom.set_string(var.clone(), new_bound);
        }
        for (var, bound) in dom.iter_int() {
            let new_bound = bound.intersect(self.options.max_bounds);
            new_dom.set_int(var.clone(), new_bound);
        }
        for v in dom.iter_bool() {
            new_dom.set_bool(v.clone());
        }
        new_dom
    }

    /// Converts the propositional formula and the definitions back to a first-order formula.
    /// This is done by replacing the Boolean literals in the propositional formula with their corresponding definitions.
    /// For example, if the propositional formula is ``(a and b) or -c``, and the definitions are ``a -> L1``, ``b -> L2``, and ``-c -> -L3``,
    /// then the resulting formula is ``(L1 and L2) or -L3``.
    /// If the propositional formula contains literals that are not defined, then they are kept as Boolean literals.
    fn to_formula(&self, ctx: &mut Context, root: &PFormula) -> Option<Node> {
        match root {
            PFormula::And(vec) => {
                let mut children = Vec::with_capacity(vec.len());
                for child in vec {
                    if let Some(node) = self.to_formula(ctx, child) {
                        children.push(node);
                    }
                }
                Some(ctx.ast().and(children))
            }
            PFormula::Or(vec) => {
                let mut children = Vec::with_capacity(vec.len());
                for child in vec {
                    if let Some(node) = self.to_formula(ctx, child) {
                        children.push(node);
                    }
                }
                Some(ctx.ast().or(children))
            }
            PFormula::Lit(l) => {
                if let Some(def) = self.defs.get(l) {
                    debug_assert!(def.defining() == *l);
                    Some(def.defined_node().clone())
                } else {
                    // Just insert a temp variable as a placeholder
                    let tvar = ctx.temp_var(Sort::Bool);
                    Some(ctx.ast().variable(tvar))
                }
            }
        }
    }
}
