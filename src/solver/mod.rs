use core::panic;
use std::time::Instant;

use crate::bounds::{BoundInferer, Bounds};
use crate::domain::Domain;
use encoder::ProblemEncoder;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

pub use options::SolverOptions;

use crate::{
    abstraction::{build_abstraction, Abstraction, LitDefinition},
    alphabet::{self, Alphabet},
    interval::Interval,
    node::{
        canonical::{canonicalize, Assignment},
        get_entailed_literals,
        smt::to_script,
        Node, NodeKind, NodeManager, NodeSubstitution, Sort, Sorted,
    },
    sat::{to_cnf, PFormula, PLit},
};

use crate::error::PublicError as Error;

mod encoder;
mod options;
mod preprocessing;
mod refine;

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

pub struct Engine {
    options: SolverOptions,
}

impl Engine {
    pub fn with_options(options: SolverOptions) -> Self {
        Self { options }
    }

    pub fn solve(&mut self, root: &Node, mngr: &mut NodeManager) -> Result<SolverResult, Error> {
        log::info!("Starting engine");
        let mut timer = Instant::now();
        log::debug!("Solving: {}", root);

        // Preprocess
        let mut preprocessor = preprocessing::Preprocessor::default();
        let preprocessed = if self.options.simplify {
            preprocessor.apply(root, self.options.preprocess_extra_passes, mngr)?
        } else {
            root.clone()
        };
        log::info!("Preprocessed ({:?})", timer.elapsed());
        if self.options.print_preprocessed {
            //let smt = ir::smt::to_smtlib(&preprocessed);
            println!("{}", to_script(&preprocessed));
        }

        // Early return if the formula is trivially sat/unsat
        if let NodeKind::Bool(v) = *preprocessed.kind() {
            return Ok(if v {
                SolverResult::Sat(Some(preprocessor.applied_substitutions().clone()))
            } else {
                SolverResult::Unsat
            });
        }

        // Canonicalize
        let formula = canonicalize(&preprocessed, mngr)?;
        log::info!("Canonicalized ({:?})", timer.elapsed());
        log::debug!("Canonicalized\n{}", formula);

        // Initialize the bounds
        let init_dom = match self.init_domain(&formula, mngr) {
            Some(bs) => bs,
            None => {
                log::info!("No valid initial bounds. Unsat.");
                return Ok(SolverResult::Unsat);
            }
        };

        timer = Instant::now();
        let abstraction = build_abstraction(&formula)?;
        log::info!("Built abstraction ({:?})", timer.elapsed());

        log::info!("Initialized bounds ({:?})", timer.elapsed());
        log::debug!("Initial bounds: {}", init_dom);

        // timer = Instant::now();

        // Initialize the alphabet
        let alphabet = alphabet::infer(&formula);
        log::info!(
            "Inferred alphabet of size {} ({:?})",
            alphabet.len(),
            timer.elapsed()
        );
        log::debug!("Alphabet: {}", alphabet);

        if self.options.dry {
            return Ok(SolverResult::Unknown);
        }

        let solver = AbstractionSolver::new(
            self.options.clone(),
            abstraction.skeleton().clone(),
            alphabet,
            init_dom,
        );

        let res = self.cegar_loop(
            solver,
            abstraction.definitions().cloned().collect_vec(),
            mngr,
        );

        panic!("Combine with preprocessing substitutions!");
    }

    fn cegar_loop(
        &mut self,
        mut solver: AbstractionSolver,
        defs: Vec<LitDefinition>,
        mngr: &mut NodeManager,
    ) -> Result<SolverResult, Error> {
        log::info!("Starting solver loop");

        // First call: check if skeleton is unsat
        // if unsat, return UNSAT
        // if sat, continue with CEGAR loop
        /*if solver.solve(mngr)?.is_unsat() {
            return Ok(SolverResult::Unsat);
        }*/

        log::debug!("Boolean Skeleton is SAT. Continuing to encode.");

        // select the initial definitions
        let defs = defs.clone();
        for d in defs {
            solver.add_definition(&d);
        }

        solver.solve(mngr)
    }

    fn init_domain(&self, fm: &Node, mngr: &mut NodeManager) -> Option<Domain> {
        let mut inferer = BoundInferer::default();
        for lit in get_entailed_literals(fm) {
            inferer.add_literal(lit.clone(), mngr)
        }

        let init_bounds = inferer.infer()?;
        // Clamp all bounds and add Booleans to the domain
        let mut domain = Domain::default();
        for v in fm.variables() {
            match v.sort() {
                Sort::Int | Sort::String => {
                    let lower = init_bounds
                        .get(&v)
                        .and_then(|b| b.lower_finite())
                        .unwrap_or(0);
                    let upper = init_bounds
                        .get(&v)
                        .and_then(|b| b.upper_finite())
                        .unwrap_or(self.options.init_upper_bound)
                        .max(lower) // at least lower
                        .max(1); // at least 1
                    let interval = Interval::new(lower, upper);
                    // Clamp the bound to max
                    let interval = interval.intersect(self.options.max_bounds);
                    match v.sort() {
                        Sort::Int => domain.set_int(v.clone(), interval),
                        Sort::String => domain.set_string(v.clone(), interval),
                        _ => unreachable!(),
                    };
                }
                Sort::Bool => domain.set_bool(v.clone()),
                Sort::RegLan => unreachable!(),
            };
        }
        Some(domain)
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Node, assign: &Assignment) -> bool {
        assign.satisfies(fm)
    }
}

struct AbstractionSolver {
    options: SolverOptions,

    cadical: cadical::Solver,

    skeleton: PFormula,
    /// The definitions of the abstraction variables
    defs: IndexMap<PLit, LitDefinition>,

    encoder: ProblemEncoder,
    next_bounds: Domain,
}

impl AbstractionSolver {
    pub fn new(
        options: SolverOptions,
        skeleton: PFormula,
        alphabet: Alphabet,
        init_bounds: Domain,
    ) -> Self {
        let mut sat_solver = cadical::Solver::default();
        let cnf = to_cnf(&skeleton);
        for clause in cnf.into_iter() {
            sat_solver.add_clause(clause);
        }
        Self {
            options,
            skeleton,
            cadical: sat_solver,
            defs: IndexMap::new(),
            encoder: ProblemEncoder::new(alphabet, IndexSet::new()),
            next_bounds: init_bounds,
        }
    }

    pub fn add_definition(&mut self, def: &LitDefinition) {
        if self.defs.contains_key(&def.defining()) {
            panic!(
                "Definition for literal {} already exists. Cannot redefine.",
                def.defining()
            );
        }
        log::debug!("Adding definition: {}", def);
        self.defs.insert(def.defining().clone(), def.clone());
    }

    fn solve(&mut self, mngr: &mut NodeManager) -> Result<SolverResult, Error> {
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

            let encoding =
                self.encoder
                    .encode(self.defs.values().cloned().into_iter(), &bounds, mngr)?;
            let (cnf, asm) = encoding.into_inner();
            log::info!("Encoded ({} clauses) ({:?})", cnf.len(), timer.elapsed());
            timer = Instant::now();
            for clause in cnf {
                self.cadical.add_clause(clause);
            }
            log::info!("Added clauses to cadical ({:?})", timer.elapsed());

            timer = Instant::now();
            let res = self.cadical.solve_with(asm.into_iter());
            log::info!("Done SAT solving: {:?} ({:?})", res, timer.elapsed());

            match res {
                Some(true) => {
                    // If SAT, check if model is a solution for the original formula.
                    let assign = self.encoder.get_model(&self.cadical);

                    log::info!("Found model: {}", assign);

                    // encoder.print_debug(&cadical);
                    let subs = NodeSubstitution::from_assignment(&assign, mngr);
                    return Ok(SolverResult::Sat(Some(subs)));
                }

                Some(false) => {
                    log::info!("Unsat");
                    let failed = self.encoder.get_failed_literals(&self.cadical);
                    log::info!("{} Failed literal(s)", failed.len());
                    log::debug!("Failed literals: {}", failed.iter().join(", "));
                    // Refine bounds. If bounds are at max, return UNSAT. Otherwise, continue with new bounds.
                    let fm = self
                        .to_formula(mngr, &self.skeleton)
                        .unwrap_or(mngr.ttrue());
                    match refine::refine_bounds(&failed, &bounds, &fm, self.options.step, mngr) {
                        refine::BoundRefinement::Refined(b) => {
                            let clamped = self.clamp_bounds_in_dom(b);
                            // if the clamped bound are equal to the bounds we used in this round, nothing changed
                            // in that case, the limit is reached
                            if clamped == bounds {
                                if self.options.unsat_on_max_bound {
                                    return Ok(SolverResult::Unsat);
                                } else {
                                    return Ok(SolverResult::Unknown);
                                }
                            } else {
                                self.next_bounds = clamped
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
                    None
                }
            }
        }
    }
}
