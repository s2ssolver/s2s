use std::cmp::max;
use std::collections::HashSet;

use std::time::Instant;

use crate::abstr::Abstraction;
use crate::bounds::Bounds;

use crate::encode::EncodingResult;
use crate::model::constraints::{Symbol, WordEquation};
use crate::solver::analysis::{init_bounds, next_bounds};

use crate::{SolverOld, SolverResult};

use crate::error::Error;

use crate::instance::Instance;

use crate::model::Sort;
use crate::model::Substitution;

use crate::sat::{to_cnf, Cnf};

use super::analysis::BoundUpdate;
use super::manager::EncodingManager;

pub(super) struct AbstractionSolver {
    instance: Instance,
    encoding_mng: EncodingManager,
    abstraction: Abstraction,
}

impl AbstractionSolver {
    pub fn new(mut instance: Instance) -> Result<Self, Error> {
        // Create the abstraction
        let abstraction = Abstraction::new(&mut instance);
        let mut cm = EncodingManager::new(&instance);
        let fm = instance.get_script().to_nnf();
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

            abstraction,
        })
    }

    /// Makes sure that the upper bounds for string variables are at least 1.
    /// This is necessary for the encoding to work correctly.
    /// If a upper bound less than 1, it is set to 1.
    fn sanitize_bounds(&self, bounds: &mut Bounds) {
        for v in self.instance.vars_of_sort(Sort::String) {
            let len_var = v.len_var().unwrap();
            if let Some(upper) = bounds.get_upper(&len_var) {
                if upper <= 0 {
                    bounds.set_upper(&len_var, 1);
                }
            }
        }
    }
}

impl SolverOld for AbstractionSolver {
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

        log::debug!("Solving formula {}", self.instance.get_script());

        let mut cadical: cadical::Solver = cadical::Solver::new();

        // Convert the skeleton to cnf and add it to the solver

        let skeleton_cnf = if !self.instance.get_script().is_conjunctive() {
            log::debug!("Skeleton {}", self.abstraction.get_skeleton());
            let cnf: Vec<Vec<i32>> = to_cnf(self.abstraction.get_skeleton(), &mut self.instance)?;
            Some(cnf)
        } else {
            None
        };
        if let Some(cnf) = &skeleton_cnf {
            log::trace!("Skeleton CNF: {:?}", cnf);
            for clause in cnf.into_iter() {
                cadical.add_clause(clause.clone());
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

            let encoding = self
                .encoding_mng
                .encode_bounded(&current_bounds, &self.instance)?;

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
                            log::info!(
                                "Done. Total time encoding/solving: {}/{} ms",
                                time_encoding,
                                time_solving
                            );
                            //self.encoding_mng
                            //    .print_debug(&cadical, self.domain_encoder.encoding());
                            let model = if self.instance.get_print_model() {
                                Some(self.encoding_mng.construct_model(&cadical, &self.instance))
                            } else {
                                None
                            };
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
                    let model = if self.instance.get_print_model() {
                        let mut model = Substitution::new();
                        model.use_defaults();
                        Some(model)
                    } else {
                        None
                    };
                    return Ok(SolverResult::Sat(model));
                }
            }

            // Prepare next round
            let ts = Instant::now();
            let mut next_bounds = match next_bounds(
                &self.encoding_mng,
                &cadical,
                &current_bounds,
                &self.instance,
                skeleton_cnf.as_ref(),
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
            self.sanitize_bounds(&mut next_bounds);
            if next_bounds == current_bounds {
                return Ok(SolverResult::Unknown);
            } else {
                current_bounds = next_bounds;
            }

            log::info!("Inferred new bounds ({} ms)", ts.elapsed().as_millis());
            if self
                .encoding_mng
                .iter_mut()
                .map(|(_, enc)| enc)
                .any(|enc| !enc.is_incremental())
            {
                // reset states if at least one solver is not incremental
                self.encoding_mng.reset();
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
