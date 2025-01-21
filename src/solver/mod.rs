use core::panic;
use std::time::Instant;

use encoder::ProblemEncoder;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

pub use options::SolverOptions;

use crate::{
    abstraction::{build_abstraction, Abstraction, LitDefinition},
    alphabet::{self, Alphabet},
    bounds::{infer::BoundInferer, Domain, Interval},
    node::{
        canonical::{canonicalize, Assignment},
        get_entailed_literals,
        smt::to_script,
        Node, NodeKind, NodeManager, NodeSubstitution, Sorted,
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
    solver: Solver,
    options: SolverOptions,
}

impl Engine {
    pub fn with_options(options: SolverOptions) -> Self {
        let solver = Solver::with_options(options.clone());
        Self { options, solver }
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
        let init_bounds = match self.init_bounds(&formula, mngr) {
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
        log::debug!("Initial bounds: {}", init_bounds);

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
            init_bounds,
        );

        self.cegar_loop(
            solver,
            abstraction.definitions().cloned().collect_vec(),
            mngr,
        )

        // if self.options.check_model && !self.check_assignment(fm, &assign) {
        //     // If the assignment is not a solution, we found a bug.
        //     panic!("The found model is invalid");
        // }
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
        if solver.solve(mngr)?.is_unsat() {
            return Ok(SolverResult::Unsat);
        }

        log::debug!("Boolean Skeleton is SAT. Continuing to encode.");

        // select the initial definitions
        let defs = defs.clone();
        for d in defs {
            solver.add_definition(&d);
        }

        solver.solve(mngr)
    }

    /// Initialize the bounds for the first round of the solver.
    /// The bounds are inferred from the entailed literals of the formula but clamped to the bounds specified in the options.
    fn init_bounds(&self, fm: &Node, mngr: &mut NodeManager) -> Option<Domain> {
        let mut inferer = BoundInferer::default();
        for lit in get_entailed_literals(fm) {
            inferer.add_literal(lit.clone(), mngr)
        }

        let mut bounds = inferer.infer()?;
        log::debug!("Inferred bounds for entailed literals: {}", bounds);
        for var in fm
            .variables()
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
            bounds.set(var.clone(), Interval::new(lower, upper));
        }
        let clamped = self.clamp_bounds(bounds);
        // Clamp the bounds to the maximum bounds, if set
        Some(clamped)
    }

    /// Check if the assignment is a solution for the formula.
    fn check_assignment(&self, fm: &Node, assign: &Assignment) -> bool {
        assign.satisfies(fm)
    }

    /// Clamp the bounds to the maximum bounds.
    fn clamp_bounds(&self, bounds: Domain) -> Domain {
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

    /// Clamp the bounds to the maximum bounds.
    fn clamp_bounds(&self, bounds: Domain) -> Domain {
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
        let init_bounds = match self.init_bounds(&formula, mngr) {
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
        log::debug!("Initial bounds: {}", init_bounds);

        // timer = Instant::now();

        // Initialize the alphabet
        let alphabet = alphabet::infer(&formula);
        log::info!("Inferred alphabet ({:?})", timer.elapsed());
        log::debug!("Alphabet: {}", alphabet);
        timer = Instant::now();

        if self.options.dry {
            return Ok(SolverResult::Unknown);
        }
        // Start CEGAR loop
        let res = self.run(&formula, abstraction, init_bounds, alphabet, mngr);

        log::info!("Done solving ({:?})", timer.elapsed());
        res
    }

    fn init_bounds(&self, fm: &Node, mngr: &mut NodeManager) -> Option<Domain> {
        let mut inferer = BoundInferer::default();
        for lit in get_entailed_literals(fm) {
            inferer.add_literal(lit, mngr)
        }

        let mut bounds = inferer.infer()?;
        log::debug!("Inferred bounds for entailed literals: {}", bounds);
        for var in fm
            .variables()
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
            bounds.set(var.clone(), Interval::new(lower, upper));
        }
        let clamped = self.clamp_bounds(bounds);
        // Clamp the bounds to the maximum bounds, if set
        Some(clamped)
    }

    fn run(
        &mut self,
        fm: &Node,
        abs: Abstraction,
        init_bounds: Domain,
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

        let mut encoder = ProblemEncoder::new(alphabet, fm.variables());

        // Initialize the bounds
        let mut bounds = init_bounds;

        let mut round = 0;

        // Start Solving Loop
        loop {
            round += 1;
            log::info!("Round {} with bounds {}", round, bounds);
            // Encode and Solve
            t = Instant::now();
            let encoding = encoder.encode(defs.clone().into_iter(), &bounds, mngr)?;
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
    fn check_assignment(&self, fm: &Node, assign: &Assignment) -> bool {
        assign.satisfies(fm)
    }

    /// Clamp the bounds to the maximum bounds.
    fn clamp_bounds(&self, bounds: Domain) -> Domain {
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
