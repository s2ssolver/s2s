use core::panic;
use std::{rc::Rc, time::Instant};

use crate::{
    domain::Domain,
    node::{
        canonical::{Assignment, AtomKind, Literal},
        Sort, VarSubstitution,
    },
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
    node::{Node, NodeManager},
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
    pub fn solve(&mut self, mngr: &mut NodeManager) -> Result<SolverAnswer, Error> {
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
                mngr,
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
                        let assign = self.encoder.get_model(&self.cadical);

                        log::info!("Encoding is SAT");
                        // encoder.print_debug(&cadical);
                        let subs = VarSubstitution::from_assignment(&assign, mngr);
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
                            .to_formula(mngr, &self.skeleton)
                            .unwrap_or(mngr.ttrue());
                        match self.refiner.refine_bounds(
                            &failed,
                            &bounds,
                            &fm,
                            self.options.step,
                            mngr,
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
    pub fn block(&mut self, asn: &Assignment) {
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
    fn to_formula(&self, mngr: &mut NodeManager, root: &PFormula) -> Option<Node> {
        match root {
            PFormula::And(vec) => {
                let mut children = Vec::with_capacity(vec.len());
                for child in vec {
                    if let Some(node) = self.to_formula(mngr, child) {
                        children.push(node);
                    }
                }
                Some(mngr.and(children))
            }
            PFormula::Or(vec) => {
                let mut children = Vec::with_capacity(vec.len());
                for child in vec {
                    if let Some(node) = self.to_formula(mngr, child) {
                        children.push(node);
                    }
                }
                Some(mngr.or(children))
            }
            PFormula::Lit(l) => {
                if let Some(def) = self.defs.get(l) {
                    debug_assert!(def.defining() == *l);
                    Some(mngr.literal(def.defined().clone()))
                } else {
                    let tvar = mngr.temp_var(Sort::Bool);
                    let atom = mngr.atom(AtomKind::Boolvar(tvar));
                    Some(mngr.literal(Literal::positive(atom)))
                }
            }
        }
    }
}
