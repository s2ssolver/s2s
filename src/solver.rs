use std::cmp::max;
use std::collections::HashMap;

use indexmap::IndexSet;

use std::time::Instant;

use crate::abstr::{Abstraction, Definition};
use crate::bounds::{Bounds, IntDomain};
use crate::encode::{
    AlignmentEncoder, ConstraintEncoder, EncodingResult, MddEncoder, NFAEncoder,
    RegularConstraintEncoder, WordEquationEncoder,
};

use crate::error::Error;

use crate::instance::Instance;
use crate::model::constraints::{Symbol, WordEquation};
use crate::model::formula::Alphabet;

use crate::model::Sort;
use crate::model::{Constraint, Substitution};

use crate::encode::domain::{get_substitutions, DomainEncoder};

use crate::sat::{neg, to_cnf, Cnf};

/// The result of a satisfiability check
pub enum SolverResult {
    /// The instance is satisfiable with the given model
    Sat(Substitution),
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
    pub fn get_model(&self) -> Option<&Substitution> {
        match self {
            SolverResult::Sat(model) => Some(model),
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

/// A solver for a problem instance.
/// A solver provides a `solve` method that takes an instance and decides whether it is satisfiable.
/// Implementations of this trait accept different kinds of instances.
// todo: Default solver for formulas.
pub trait Solver {
    /// Solve the given instance.
    fn solve(&mut self) -> Result<SolverResult, Error>;
}

/// Returns a solver for the given instance.
pub fn get_solver(inst: Instance) -> Result<Box<dyn Solver>, Error> {
    AbstractionSolver::new(inst).map(|s| Box::new(s) as Box<dyn Solver>)
}

struct AbstractionSolver {
    instance: Instance,
    alphabet: IndexSet<char>,
    encoders: HashMap<Definition, Box<dyn ConstraintEncoder>>,
    abstraction: Abstraction,
    domain_encoder: DomainEncoder,
}

impl AbstractionSolver {
    /// Instatiates a new encoder for the given constraint.
    fn encoder_for_constraint(con: &Constraint) -> Result<Box<dyn ConstraintEncoder>, Error> {
        match con {
            Constraint::WordEquation(eq) => Ok(Box::new(AlignmentEncoder::new(eq.clone()))),
            Constraint::LinearConstraint(lc) => Ok(Box::new(MddEncoder::new(lc.clone()))),
            Constraint::RegularConstraint(rc) => Ok(Box::new(NFAEncoder::new(rc.clone())?)),
        }
    }

    fn new(mut instance: Instance) -> Result<Self, Error> {
        let mut alphabet = instance.get_formula().alphabet();
        // Make sure the alphabet contains at least one character
        alphabet.insert('a');

        // Instantiate the Domain encoder
        let dom_encoder = DomainEncoder::new(alphabet.clone());

        // Create the abstraction
        let abstraction = Abstraction::create(&mut instance)?;

        // Instantiate the encoders
        let mut encoders = HashMap::new();
        for d in abstraction.get_definitions().iter() {
            let constraint = Constraint::try_from(d.get_pred().clone())?;
            let encoder = Self::encoder_for_constraint(&constraint)?;
            encoders.insert(d.clone(), encoder);
        }

        Ok(Self {
            instance,
            alphabet,
            encoders,
            abstraction,
            domain_encoder: dom_encoder,
        })
    }

    /// Encodes the problem instance with the given bounds.
    /// Returns the encoding result.
    fn encode_bounded(&mut self, bounds: &Bounds) -> Result<EncodingResult, Error> {
        let mut encoding = EncodingResult::empty();
        if self.encoders.is_empty() {
            return Ok(EncodingResult::Trivial(true));
        }

        let mut bounds = bounds.clone();
        if self.encoders.len() == 1 {
            // Check if the only constraint is a word equation
            if let Some(Constraint::WordEquation(eq)) = self
                .encoders
                .keys()
                .next()
                .and_then(|d| d.get_pred().clone().try_into().ok())
            {
                bounds = sharpen_bounds(&eq, &bounds, &self.instance)
            }
        }

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

        if self.instance.get_formula().is_conjunctive() {
            for (_, enc) in self.encoders.iter_mut() {
                let res = enc.encode(&bounds, dom)?;
                encoding.join(res);
            }
        } else {
            for (d, enc) in self.encoders.iter_mut() {
                let mut res = enc.encode(&bounds, dom)?;
                // Insert the negation of the definitional boolean var into all clauses
                let def_pvar = self.domain_encoder.get_bools()[d.get_var()];
                res.iter_clauses_mut().for_each(|c| c.push(neg(def_pvar)));
                encoding.join(res);
            }
        }

        Ok(encoding)
    }

    // Reset all states
    fn reset(&mut self) {
        self.domain_encoder = DomainEncoder::new(self.alphabet.clone());
        for (_, encoder) in self.encoders.iter_mut() {
            encoder.reset();
        }
    }

    fn find_limit_upper_bound(&self) -> Result<Bounds, Error> {
        let mut limit_bounds = Bounds::infer(self.instance.get_formula(), &self.instance)?;
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
    fn next_bounds(&self, current_bounds: Option<&Bounds>, limit_bounds: &Bounds) -> Bounds {
        let mut next_bounds = match current_bounds {
            Some(c) => c.clone(),
            None => {
                let mut current_bounds = Bounds::new();
                for v in self.instance.vars_of_sort(Sort::String) {
                    let len_var = v.len_var().unwrap();
                    current_bounds.set(
                        &len_var,
                        IntDomain::Bounded(0, self.instance.get_start_bound() as isize),
                    );
                }
                current_bounds
            }
        };
        next_bounds.next_square_uppers();

        while next_bounds.any_empty() && !self.exeed_limit_bounds(&next_bounds, limit_bounds) {
            next_bounds.next_square_uppers();
            next_bounds = next_bounds.intersect(limit_bounds);
        }

        if let Some(upper) = self.instance.get_upper_threshold() {
            next_bounds.clamp_uppers(upper as isize);
        }
        next_bounds
    }

    /// Returns true if the current upper bounds are greater than the limit upper bounds.
    fn exeed_limit_bounds(&self, current_bounds: &Bounds, limit_bounds: &Bounds) -> bool {
        for v in self.instance.vars_of_sort(Sort::Int) {
            match (
                current_bounds.get(v).get_upper(),
                limit_bounds.get(v).get_upper(),
            ) {
                (Some(c), Some(l)) => {
                    if c <= l {
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

    /// Returns true if the current upper bounds are greater than the given threshold.
    fn bounds_exceed_threshold(&self, current_bounds: &Bounds, threshold: usize) -> bool {
        for v in self.instance.vars_of_sort(Sort::Int) {
            match current_bounds.get(v).get_upper() {
                Some(c) => {
                    if c <= threshold as isize {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl Solver for AbstractionSolver {
    fn solve(&mut self) -> Result<SolverResult, Error> {
        // Encode the booleans
        self.domain_encoder.init_booleans(&self.instance);
        let limit_bounds = self.find_limit_upper_bound()?;
        log::info!("Found limit bounds: {}", limit_bounds);

        if limit_bounds.any_empty() {
            log::info!("Empty upper bounds, unsat");
            return Ok(SolverResult::Unsat);
        }

        let mut current_bounds = self.next_bounds(None, &limit_bounds);

        log::info!(
            "Started solving loop for system of {} equations, alphabet size {}",
            self.instance.get_formula().num_atoms(),
            self.alphabet.len()
        );
        log::debug!("{}", self.instance.get_formula());

        let mut cadical: cadical::Solver = cadical::Solver::new();

        if !self.instance.get_formula().is_conjunctive() {
            // Convert the skeleton to cnf and add it to the solver
            let ts = Instant::now();
            let cnf = to_cnf(self.abstraction.get_skeleton(), &mut self.instance)?;
            log::info!(
                "Converted Boolean skeleton into cnf ({} clauses) in {} ms",
                cnf.len(),
                ts.elapsed().as_millis()
            );
            for clause in cnf.into_iter() {
                cadical.add_clause(clause);
            }
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
                                if self.exeed_limit_bounds(&current_bounds, &limit_bounds) {
                                    // We reached the limit bounds, but did not find a solution.
                                    // This means no solution exists.
                                    // Return unsat
                                    log::info!("Reached limit bounds");
                                    return Ok(SolverResult::Unsat);
                                }
                                if let Some(threshold) = self.instance.get_upper_threshold() {
                                    if self.bounds_exceed_threshold(&current_bounds, threshold) {
                                        // We reached the user-imposed upper bound and did not find a solution
                                        // Return unknown
                                        log::info!("Reached set threshold bound");
                                        return Ok(SolverResult::Unknown);
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
            } else {
                log::info!("Empty bounds, skipping");
            }

            // Prepare next round
            current_bounds = self.next_bounds(Some(&current_bounds), &limit_bounds);

            if self.encoders.values().any(|enc| !enc.is_incremental()) {
                // reset states if at least one solver is not incremental
                self.reset();
                cadical = cadical::Solver::new();
                log::debug!("Reset state");
            }
        }
    }
}

fn sharpen_bounds(eq: &WordEquation, bounds: &Bounds, vars: &Instance) -> Bounds {
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
