use std::cmp::max;

use indexmap::IndexSet;

use std::time::Instant;

use crate::abstr::Abstraction;
use crate::bounds::{infer, Bounds, IntDomain};

use crate::encode::EncodingResult;
use crate::model::constraints::{Symbol, WordEquation};
use crate::{Solver, SolverResult};

use crate::error::Error;

use crate::instance::Instance;

use crate::model::formula::Alphabet;

use crate::model::Sort;
use crate::model::{Constraint, Substitution};

use crate::encode::domain::{get_substitutions, DomainEncoder};

use crate::sat::{to_cnf, Cnf};

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

        for (def, lit) in abstraction.definitions().iter() {
            cm.add(lit, *def, &instance)?;
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
        let subs_cnf = self.domain_encoder.encode(&bounds, &self.instance);
        log::debug!(
            "Encoded domain for all variables with {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );
        encoding.join(subs_cnf);
        let dom = self.domain_encoder.encoding();

        for (ctx, enc) in self.encoding_mng.iter() {
            let mut res = enc.encode(&bounds, dom)?;
            let def_lit = ctx.definitional();
            let watcher = ctx.watcher();
            // def_lit -> encoding
            // watcher -> (def_lit -> encoding)
            // Insert the negation of def_lit and watcher into all clauses

            for ref mut clause in res.iter_clauses_mut() {
                clause.push(-watcher);
                clause.push(-def_lit);
            }
            // Append encoding to results
            encoding.join(res);
            encoding.add_assumption(def_lit);
            encoding.add_assumption(watcher);
        }

        Ok(encoding)
    }

    // Reset all states
    fn reset(&mut self) {
        self.domain_encoder = DomainEncoder::new(self.alphabet.clone());
        for (_, encoder) in self.encoding_mng.iter() {
            encoder.reset();
        }
    }

    fn find_limit_upper_bound(&self) -> Result<Bounds, Error> {
        let mut limit_bounds = if self.instance.get_formula().is_conjunctive() {
            let asserted_constr = self
                .instance
                .get_formula()
                .to_nnf()
                .asserted_literals()
                .iter()
                .filter_map(|lit| self.encoding_mng.for_literal(lit))
                .map(|ctx| ctx.constraint().clone())
                .collect::<Vec<_>>();

            infer(&asserted_constr, &self.instance)?
        } else {
            Bounds::new()
        };

        // Make sure upper bounds for string variables are at least one, otherwise the encoding is not correct.
        // This will have negative effects on the performance of the solver, but avoids having to treat edge cases in the encoding(s).
        for v in self.instance.vars_of_sort(Sort::Int) {
            if v.is_len_var() {
                if let Some(0) = limit_bounds.get(v).get_upper() {
                    log::trace!("Setting upper bound for {} from 0 to 1", v);
                    limit_bounds.set_upper(v, 1);
                }
            }
        }
        Ok(limit_bounds)
    }

    /// Returns the next bounds to be used in the next round, based on the current bounds and the limit bounds.
    /// If current bounds are None, the next bounds will be the first bounds to be used.
    /// If the instance has an upper threshold, the upper bounds are clamped to the threshold.
    fn next_bounds(&self, current_bounds: Option<&Bounds>, limit_bounds: &Bounds) -> BoundUpdate {
        let mut next_bounds = match current_bounds {
            Some(c) => {
                if self.bounds_reach_threshold(c) {
                    // No need to go further, we reached the threshold
                    return BoundUpdate::ThresholdReached;
                }
                if self.bounds_reach_limit(c, limit_bounds) {
                    // No need to go further, we reached the limit
                    return BoundUpdate::LimitReached;
                }
                c.clone()
            }
            None => {
                // Initialize
                let mut current_bounds = Bounds::new();
                for v in self.instance.vars_of_sort(Sort::String) {
                    let len_var = v.len_var().unwrap();
                    let upper = self.instance.get_start_bound() as isize;
                    let lower = limit_bounds.get_lower(&len_var).unwrap_or(0);
                    let upper = max(upper, lower);
                    current_bounds.set(&len_var, IntDomain::Bounded(0, upper));
                }
                return BoundUpdate::Next(current_bounds);
            }
        };
        next_bounds.next_square_uppers();

        while next_bounds.any_empty() && !self.bounds_reach_limit(&next_bounds, limit_bounds) {
            next_bounds.next_square_uppers();
            next_bounds = next_bounds.intersect(limit_bounds);
        }

        // Clamp upper bounds to threshold
        if let Some(upper) = self.instance.get_upper_threshold() {
            next_bounds.clamp_uppers(upper as isize);
        }
        BoundUpdate::Next(next_bounds)
    }

    /// Returns true if the current upper bounds are equal to or greater than the limit upper bounds.
    fn bounds_reach_limit(&self, current_bounds: &Bounds, limit_bounds: &Bounds) -> bool {
        for v in self.instance.vars_of_sort(Sort::Int) {
            match (
                current_bounds.get(v).get_upper(),
                limit_bounds.get(v).get_upper(),
            ) {
                (Some(c), Some(l)) => {
                    if c < l {
                        return false;
                    }
                }
                (Some(_), None) => return false,
                (None, Some(_)) => return false,
                (None, None) => (),
            }
        }
        true
    }

    /// Returns true if the current upper bounds are greater than or equal to the threshold given in the instance.
    fn bounds_reach_threshold(&self, current_bounds: &Bounds) -> bool {
        if let Some(threshold) = self.instance.get_upper_threshold() {
            for v in self.instance.vars_of_sort(Sort::Int) {
                match current_bounds.get(v).get_upper() {
                    Some(c) => {
                        if c < threshold as isize {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        } else {
            false
        }
    }
}

impl Solver for AbstractionSolver {
    fn solve(&mut self) -> Result<SolverResult, Error> {
        log::debug!("Started solving");

        let limit_bounds = self.find_limit_upper_bound()?;
        log::info!("Found limit bounds: {}", limit_bounds);

        if limit_bounds.any_empty() {
            log::info!("Empty upper bounds, unsat");
            return Ok(SolverResult::Unsat);
        }

        // First call guarantees to returns some bounds
        let mut current_bounds = self.next_bounds(None, &limit_bounds).unwrap();

        log::info!(
            "Started solving loop for system of {} equations, alphabet size {}",
            self.instance.get_formula().num_atoms(),
            self.alphabet.len()
        );
        log::debug!("{}", self.instance.get_formula());

        let mut cadical: cadical::Solver = cadical::Solver::new();

        // Convert the skeleton to cnf and add it to the solver
        let ts = Instant::now();
        log::info!("Skeleton {}", self.abstraction.get_skeleton());
        let cnf = to_cnf(self.abstraction.get_skeleton(), &mut self.instance)?;
        log::info!(
            "Converted Boolean skeleton into cnf ({} clauses) in {} ms",
            cnf.len(),
            ts.elapsed().as_millis()
        );
        log::trace!("CNF: {:?}", cnf);
        for clause in cnf.into_iter() {
            cadical.add_clause(clause);
        }

        // Check if the skeleton is unsat
        if let Some(false) = cadical.solve() {
            log::info!("Skeleton is unsat");
            return Ok(SolverResult::Unsat);
        }

        let mut time_encoding = 0;
        let mut time_solving = 0;
        let mut fm = Cnf::new();

        loop {
            log::info!("Current bounds {}", current_bounds);
            if !current_bounds.any_empty() {
                let ts = Instant::now();

                let encoding = self.encode_bounded(&current_bounds)?;
                let elapsed = ts.elapsed().as_millis();
                log::info!("Encoding took {} ms", elapsed);
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
                                let mut model = Substitution::from(get_substitutions(
                                    self.domain_encoder.encoding(),
                                    &self.instance,
                                    &cadical,
                                ));
                                // Map variables that were removed in preprocessing to their default value
                                model.use_defaults();

                                log::info!(
                                    "Done. Total time encoding/solving: {}/{} ms",
                                    time_encoding,
                                    time_solving
                                );
                                return Ok(SolverResult::Sat(model));
                            }
                            Some(false) => {

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
            } else {
                log::info!("Empty bounds, skipping");
            }

            // Prepare next round
            current_bounds = match self.next_bounds(Some(&current_bounds), &limit_bounds) {
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

            if self
                .encoding_mng
                .iter()
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

/// The result of increasing the bounds used for solving.
enum BoundUpdate {
    /// The next bounds to be used
    Next(Bounds),
    /// The current bounds are sufficient, if the instance is satisfiable
    LimitReached,
    /// User-imposed threshold reached, cannot increase bounds further
    ThresholdReached,
}

impl BoundUpdate {
    fn unwrap(self) -> Bounds {
        match self {
            BoundUpdate::Next(b) => b,
            BoundUpdate::LimitReached => panic!("Called unwarp on BoundUpdate::LimitReached"),
            BoundUpdate::ThresholdReached => {
                panic!("Called unwarp on BoundUpdate::ThresholdReached")
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
