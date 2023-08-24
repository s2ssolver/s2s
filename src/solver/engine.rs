use std::cmp::max;
use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use std::time::Instant;

use crate::abstr::Abstraction;
use crate::bounds::Bounds;

use crate::encode::EncodingResult;
use crate::model::constraints::{Symbol, WordEquation};
use crate::solver::analysis::{init_bounds, next_bounds};
use crate::solver::manager::EncodingContext;
use crate::{Solver, SolverResult};

use crate::error::Error;

use crate::instance::Instance;

use crate::model::formula::Alphabet;

use crate::model::Sort;
use crate::model::Substitution;

use crate::encode::domain::{get_int_substitutions, get_str_substitutions, DomainEncoder};

use crate::sat::{to_cnf, Cnf, PLit};

use super::analysis::BoundUpdate;
use super::manager::EncodingManager;

pub(super) struct AbstractionSolver {
    instance: Instance,
    alphabet: IndexSet<char>,
    encoding_mng: EncodingManager,
    abstraction: Abstraction,
    domain_encoder: DomainEncoder,
}

impl AbstractionSolver {
    pub fn new(mut instance: Instance) -> Result<Self, Error> {
        let mut alphabet = instance.get_formula().alphabet();
        // Make sure the alphabet contains at least one character

        let mut next_chr: u32 = 'a' as u32;

        for _ in 0..instance.get_formula().vars().len() {
            while alphabet.contains(&char::from_u32(next_chr).unwrap()) {
                next_chr += 1;
            }
            let chr = char::from_u32(next_chr).unwrap();
            alphabet.insert(chr);
        }
        log::debug!("Alphabet: {:?}", alphabet);

        // Instantiate the Domain encoder
        let dom_encoder = DomainEncoder::new(alphabet.clone());

        // Create the abstraction
        let abstraction = Abstraction::new(&mut instance);
        let mut cm = EncodingManager::new();
        let fm = instance.get_formula().to_nnf();
        let asserted_lits = fm
            .asserted_literals()
            .iter()
            .cloned()
            .collect::<HashSet<_>>();
        for (def, lit) in abstraction.definitions().iter() {
            cm.add(lit, *def, &mut instance, asserted_lits.contains(&lit))?;
        }

        Ok(Self {
            instance,
            encoding_mng: cm,
            alphabet,

            abstraction,
            domain_encoder: dom_encoder,
        })
    }

    /// Encodes the problem instance with the given bounds.
    /// Returns the encoding result.
    fn encode_bounded(&mut self, bounds: &Bounds) -> Result<EncodingResult, Error> {
        let mut encoding = EncodingResult::empty();
        if self.encoding_mng.num_constraints() == 0 {
            return Ok(EncodingResult::Trivial(true));
        }

        // Check if the only constraint is a single (positive) word equation adn call sharpen_bounds

        // Encode the domain
        let ts = Instant::now();
        let subs_cnf = self.domain_encoder.encode(bounds, &self.instance);
        log::debug!(
            "Encoded domain for all variables with {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );

        encoding.join(subs_cnf);
        let dom = self.domain_encoder.encoding();

        let mut assumptions: IndexMap<EncodingContext, Vec<PLit>> = IndexMap::new();
        for (ctx, enc) in self.encoding_mng.iter_mut() {
            let ts = Instant::now();
            let mut res = enc.encode(bounds, dom)?;

            let def_lit = ctx.definitional();
            let watcher = ctx.watcher();
            // def_lit -> encoding
            // watcher -> (def_lit -> encoding)
            // Insert the negation of def_lit and watcher into all clauses
            if !self.instance.get_formula().is_conjunctive() {
                log::debug!("Distributing neg. defintional {}", -def_lit);
            }

            for ref mut clause in res.iter_clauses_mut() {
                clause.push(-watcher);
                if !self.instance.get_formula().is_conjunctive() {
                    clause.push(-def_lit);
                }
            }

            // Register the assumptions
            for assm in res.assumptions() {
                assumptions.entry(ctx.clone()).or_default().push(assm);
            }
            log::debug!(
                "Encoded: {}. ({} clauses, {} ms)",
                ctx.constraint(),
                res.clauses(),
                ts.elapsed().as_millis()
            );
            // Append encoding to results
            encoding.join(res);
            encoding.add_assumption(watcher);
        }
        // Register assumptions
        for (ctx, asms) in assumptions.into_iter() {
            for asm in asms.into_iter() {
                self.encoding_mng.register_assumptions(&ctx, &asm);
            }
        }

        Ok(encoding)
    }

    // Reset all states
    fn reset(&mut self) {
        self.domain_encoder = DomainEncoder::new(self.alphabet.clone());
        for (_, encoder) in self.encoding_mng.iter_mut() {
            encoder.reset();
        }
    }

    /// Makes sure that the upper bounds for string variables are at least 1 and the lower bounds are always 0.
    /// This is necessary for the encoding to work correctly.
    /// If these properties are not satisfied, bugs that lead to soundness issues are triggered:
    /// - The NFA encoding does not respect the lower bound assignment
    /// - The WEQ encoding seems to fail somewhere if an upper bound of 0 is set
    /// If a upper bound less than 1, it is set to 1.
    fn sanitize_bounds(&self, bounds: &mut Bounds) {
        for v in self.instance.vars_of_sort(Sort::String) {
            let len_var = v.len_var().unwrap();
            if let Some(upper) = bounds.get_upper(&len_var) {
                if upper <= 0 {
                    bounds.set_upper(&len_var, 1);
                }
            }
            bounds.set_lower(&len_var, 0);
        }
    }
}

impl Solver for AbstractionSolver {
    fn solve(&mut self) -> Result<SolverResult, Error> {
        log::debug!("Started solving");

        // First call guarantees to returns some bounds
        let mut current_bounds = match init_bounds(&self.encoding_mng, &self.instance)? {
            BoundUpdate::Next(b) => b,
            BoundUpdate::LimitReached => return Ok(SolverResult::Unsat),
            BoundUpdate::ThresholdReached => return Ok(SolverResult::Unknown),
        };

        // Sanitize bounds
        self.sanitize_bounds(&mut current_bounds);

        log::debug!("Solving formula {}", self.instance.get_formula());

        let mut cadical: cadical::Solver = cadical::Solver::new();

        // Convert the skeleton to cnf and add it to the solver

        if !self.instance.get_formula().is_conjunctive() {
            log::debug!("Skeleton {}", self.abstraction.get_skeleton());
            let cnf = to_cnf(self.abstraction.get_skeleton(), &mut self.instance)?;

            log::trace!("CNF: {:?}", cnf);
            for clause in cnf.into_iter() {
                cadical.add_clause(clause);
            }
            // Check if the skeleton is unsat
            if let Some(false) = cadical.solve() {
                log::info!("Skeleton is unsat");
                return Ok(SolverResult::Unsat);
            }
        } else {
            log::debug!("Formula is conjunctive, skipping skeleton encoding");
        }

        let mut time_encoding = 0;
        let mut time_solving = 0;
        let mut fm = Cnf::new();

        loop {
            log::debug!("Current bounds {}", current_bounds);

            let ts = Instant::now();
            self.encoding_mng.clear_assumptions();
            let encoding = self.encode_bounded(&current_bounds)?;
            let elapsed = ts.elapsed().as_millis();
            log::info!("Encoded in {} ms", elapsed);
            time_encoding += elapsed;

            match encoding {
                EncodingResult::Cnf(clauses, assms) => {
                    let n_clauses = clauses.len();
                    let ts = Instant::now();
                    fm.extend(clauses.clone());

                    for clause in clauses.into_iter() {
                        cadical.add_clause(clause);
                    }

                    let t_adding = ts.elapsed().as_millis();
                    log::info!(
                        "Added {} (total {}) clauses in {} ms",
                        n_clauses,
                        cadical.num_clauses(),
                        t_adding
                    );

                    time_encoding += t_adding;
                    let ts = Instant::now();

                    let res = cadical.solve_with(assms.iter().cloned());

                    let t_solving = ts.elapsed().as_millis();
                    log::info!(
                        "Done SAT solving: {} ({}ms)",
                        res.unwrap_or(false),
                        t_solving
                    );
                    time_solving += t_solving;
                    match res {
                        Some(true) => {
                            let mut model = Substitution::from(get_str_substitutions(
                                self.domain_encoder.encoding(),
                                &self.instance,
                                &cadical,
                            ));
                            let int_model = Substitution::from(get_int_substitutions(
                                self.domain_encoder.encoding(),
                                &cadical,
                            ));
                            model = model.compose(&int_model);
                            // Map variables that were removed in preprocessing to their default value
                            model.use_defaults();

                            log::info!(
                                "Done. Total time encoding/solving: {}/{} ms",
                                time_encoding,
                                time_solving
                            );
                            //self.encoding_mng
                            //    .print_debug(&cadical, self.domain_encoder.encoding());
                            return Ok(SolverResult::Sat(model));
                        }
                        Some(false) => {
                            for asm in assms {
                                if cadical.failed(asm) {
                                    //pr!intln!("Failed assumption {}", asm);
                                }
                            }
                            // Do nothing, continue with next round
                        }
                        None => {
                            return Err(Error::SolverError(
                                "SAT Solver returned unknown".to_string(),
                            ))
                        }
                    }
                }
                EncodingResult::Trivial(false) => return Ok(SolverResult::Unsat),
                EncodingResult::Trivial(true) => {
                    let mut model = Substitution::new();
                    model.use_defaults();
                    return Ok(SolverResult::Sat(model));
                }
            }

            // Prepare next round
            let ts = Instant::now();
            current_bounds = match next_bounds(
                &self.encoding_mng,
                &cadical,
                &current_bounds,
                self.instance.get_upper_threshold(),
            )? {
                BoundUpdate::Next(b) => b,
                BoundUpdate::LimitReached => {
                    log::info!("Reached limit bounds, unsat");
                    return Ok(SolverResult::Unsat);
                }
                BoundUpdate::ThresholdReached => {
                    log::info!("Reached threshold, unknown");
                    return Ok(SolverResult::Unknown);
                }
            };
            // Sanitize bounds
            self.sanitize_bounds(&mut current_bounds);
            log::info!("Inferred new bounds ({} ms)", ts.elapsed().as_millis());
            if self
                .encoding_mng
                .iter_mut()
                .map(|(_, enc)| enc)
                .any(|enc| !enc.is_incremental())
            {
                // reset states if at least one solver is not incremental
                self.reset();
                cadical = cadical::Solver::new();
                log::debug!("Reset state");
            }
        }
    }
}

fn _sharpen_bounds(eq: &WordEquation, bounds: &Bounds, vars: &Instance) -> Bounds {
    let mut new_bounds = bounds.clone();
    // Todo: Cache this or do linearly
    let mut abs_consts: isize = 0;
    for c in eq.alphabet() {
        let rhs_c = eq.rhs().count(&Symbol::Constant(c)) as isize;
        let lhs_c = eq.lhs().count(&Symbol::Constant(c)) as isize;
        abs_consts += rhs_c - lhs_c;
    }

    for var_k in vars.vars_of_sort(Sort::String) {
        let var_k_len = var_k.len_var().unwrap();
        let denominator = eq.lhs().count(&Symbol::Variable(var_k.clone())) as isize
            - eq.rhs().count(&Symbol::Variable(var_k.clone())) as isize;
        if denominator == 0 {
            continue;
        }
        let mut abs_k: isize = 0;
        for var_j in vars.vars_of_sort(Sort::String) {
            if var_j == var_k {
                continue;
            }
            let var_j_len = var_j.len_var().unwrap();
            let abs_j = eq.lhs().count(&Symbol::Variable(var_j.clone())) as isize
                - eq.rhs().count(&Symbol::Variable(var_j.clone())) as isize;
            if abs_j * denominator < 0 {
                abs_k += abs_j * bounds.get_upper(&var_j_len).unwrap();
            }
        }
        let sharpened = std::cmp::max((abs_consts - abs_k) / denominator, 0);
        if sharpened < bounds.get_upper(&var_k_len).unwrap_or(isize::MAX) {
            new_bounds.set_upper(&var_k_len, max(sharpened, 1));
        }
    }
    new_bounds
}
