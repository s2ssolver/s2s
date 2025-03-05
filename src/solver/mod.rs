use core::panic;
use std::time::Instant;

use crate::bounds::BoundInferer;
use crate::domain::Domain;
use encoder::DefintionEncoder;

use indexmap::IndexMap;
use itertools::Itertools;

pub use options::SolverOptions;
use refine::BoundRefiner;

use crate::{
    abstraction::{build_abstraction, LitDefinition},
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

/// The result of a satisfiability check.
/// Can be either of
/// - `Sat` if the instance is satisfiable. The model, if given, is a solution to the instance.
/// - `Unsat` if the instance is unsatisfiable
/// - `Unknown` if the solver could not determine the satisfiability of the instance
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

/// The main solver engine.
/// The engine is responsible for solving a given formula.
pub struct Engine {
    options: SolverOptions,
}

impl Engine {
    pub fn with_options(options: SolverOptions) -> Self {
        Self { options }
    }

    /// Solve the given formula.
    /// Returns the result of the satisfiability check, or an error if the solver failed.
    pub fn solve(&mut self, root: &Node, mngr: &mut NodeManager) -> Result<SolverResult, Error> {
        log::info!("Starting engine");

        log::debug!("Solving: {}", root);

        let timer = Instant::now();

        // Preprocess
        let mut preprocessor = preprocessing::Preprocessor::default();
        let preprocessed = if self.options.simplify {
            preprocessor.apply(root, self.options.preprocess_extra_passes, mngr)?
        } else {
            root.clone()
        };

        // These are the substitutions applied by the preprocessor
        // We need to store them and re-apply them to the model of the preprocessed formula, to get the model of the original formula
        let prepr_subst = preprocessor.applied_substitutions().clone();

        // If the 'print_preprocessed' option is set, print the preprocessed formula
        if self.options.print_preprocessed {
            println!("{}", to_script(&preprocessed));
        }

        // Early return if the formula is trivially sat/unsat
        if let NodeKind::Bool(v) = *preprocessed.kind() {
            return Ok(if v {
                SolverResult::Sat(Some(prepr_subst))
            } else {
                SolverResult::Unsat
            });
        }

        // Canonicalize.
        // This brings the formula into a normal that the solver understands.
        let canonical = canonicalize(&preprocessed, mngr)?;
        log::debug!("Canonicalized\n{}", canonical);

        // Initialize the alphabet
        let alphabet = alphabet::infer(&canonical);
        log::info!("Inferred alphabet of size {}", alphabet.len(),);
        log::debug!("Alphabet: {}", alphabet);
        log::info!("Done preprocessing. ({:?})", timer.elapsed());

        // If the 'dry' option is set, return Unknown
        if self.options.dry {
            return Ok(SolverResult::Unknown);
        }

        // Run the CEGAR loop.
        let res = match self.cegar_loop(&canonical, alphabet, mngr)? {
            SolverResult::Sat(model) => {
                let model = model.map(|m| prepr_subst.compose(m, mngr));
                SolverResult::Sat(model)
            }
            SolverResult::Unsat => SolverResult::Unsat,
            SolverResult::Unknown => SolverResult::Unknown,
        };
        Ok(res)
    }

    /// The main CEGAR loop.
    /// This function implements the Counter-Example Guided Abstraction Refinement loop.
    /// The function first builds the Boolean abstraction of the formula, which consists of a skeleton formula and a set of definitions.
    /// Each definition is a (bi-)implication between a Boolean literal in the skeleton and a first-order literal of the formula.
    /// The loop then iteratively solves an over-approximation by encoding the skeleton and and a subset of the definitions.
    /// If the over-abstraction is satisfiable, the model is checked against the original formula.
    /// If the model satisfies the formula, the formula is satisfiable.
    /// If the model does not satisfy the formula, then the model is used to refine the abstraction.
    /// The loop continues until the formula is proven to be unsatisfiable, or the solver gives up.
    fn cegar_loop(
        &mut self,
        fm: &Node,
        alph: Alphabet,
        mngr: &mut NodeManager,
    ) -> Result<SolverResult, Error> {
        // Initialize domain
        let init_dom = match self.init_domain(&fm, mngr) {
            Some(bs) => bs,
            None => {
                log::info!("No valid initial bounds. Unsat.");
                return Ok(SolverResult::Unsat);
            }
        };

        // Build the abstraction.
        // This is the skeleton of the formula.
        let abstraction = build_abstraction(&fm)?;

        // Initialize the solver.
        // Initially, it only knows the skeleton and the alphabet.
        let mut solver = Solver::new(
            self.options.clone(),
            abstraction.skeleton().clone(),
            alph,
            init_dom,
        );

        // The set of definitions to encode
        // Every definition is a (bi-)implication between a Boolean literal and a first-order literal that needs to be encoded
        let mut defs = abstraction.definitions().cloned().collect_vec();

        loop {
            // Try to solve the current over-approximation. The first call only contains the skeleton.
            match solver.solve(mngr)? {
                SolverResult::Sat(subs) => {
                    // SAT, check if the model is a solution for the original formula
                    let model = subs.unwrap();
                    let assign = model.clone().into();
                    log::info!("Found model for over-approximation");
                    if self.check_assignment(&fm, &assign) {
                        // If the model satisfies the formula, we are done
                        return Ok(SolverResult::Sat(Some(model)));
                    } else {
                        // Over-approximation is SAT, but model does not satisfy the formula
                        // Pick the next definitions to encode
                        log::info!("Model does not satisfy the formula");
                        let next = self.pick_defs(fm, &assign, &defs);
                        if next.is_empty() {
                            // In the future, this should block the current assignment and continue
                            log::error!("No more definitions to add. Returning Unknown");
                            return Ok(SolverResult::Unknown);
                        } else {
                            // Add the next definitions to the solver
                            for d in next {
                                log::info!("Adding literal: {}", d);
                                solver.add_definition(&d);
                                defs.retain(|def| def.defining() != d.defining());
                            }
                        }
                    }
                }
                SolverResult::Unsat => return Ok(SolverResult::Unsat), // Over-approximation is UNSAT, the formula is UNSAT
                SolverResult::Unknown => return Ok(SolverResult::Unknown),
            }
        }
    }

    /// Initialize the domain of all variables in the formula.
    /// The domain is the range of values that a variable can take.
    /// The domain is encoded as the first step of the encoding.
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

    /// Pick the next definition(s) to encode.
    /// Currently, this is a no-op, and just returns the input definitions.
    /// That is, all definitions are encoded after the first iteration.
    fn pick_defs<'a>(
        &self,
        _fm: &Node,
        _assign: &Assignment,
        defs: &'a [LitDefinition],
    ) -> Vec<LitDefinition> {
        defs.to_vec()
    }
}

struct Solver {
    options: SolverOptions,

    cadical: cadical::Solver,

    skeleton: PFormula,
    /// The definitions of the abstraction variables
    defs: IndexMap<PLit, LitDefinition>,

    encoder: DefintionEncoder,
    next_bounds: Domain,

    refiner: BoundRefiner,
}

impl Solver {
    pub fn new(
        options: SolverOptions,
        skeleton: PFormula,
        alphabet: Alphabet,
        init_bounds: Domain,
    ) -> Self {
        let mut sat_solver = cadical::Solver::default();
        let cnf = to_cnf(&skeleton);
        let refiner = BoundRefiner::new(cnf.clone());
        for clause in cnf.into_iter() {
            sat_solver.add_clause(clause);
        }
        Self {
            options,
            skeleton,
            cadical: sat_solver,
            refiner,
            defs: IndexMap::new(),
            encoder: DefintionEncoder::new(alphabet),
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
            let res = self.cadical.solve_with(asm);
            log::info!("Done SAT solving: {:?} ({:?})", res, timer.elapsed());

            match res {
                Some(true) => {
                    // If SAT, check if model is a solution for the original formula.
                    let assign = self.encoder.get_model(&self.cadical);

                    log::info!("Encoding is SAT");
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
                    match self
                        .refiner
                        .refine_bounds(&failed, &bounds, &fm, self.options.step, mngr)
                    {
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
