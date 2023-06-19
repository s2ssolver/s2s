use std::cmp::max;
use std::collections::HashMap;

use indexmap::IndexSet;

use std::time::Instant;

use crate::bounds::{Bounds, IntDomain};
use crate::encode::{
    AlignmentEncoder, ConstraintEncoder, EncodingResult, MddEncoder, WordEquationEncoder,
};

use crate::error::Error;
use crate::model::formula::Atom;
use crate::model::words::Symbol;
use crate::model::words::WordEquation;
use crate::model::Substitution;
use crate::model::{Constraint, Sort, VarManager};

use crate::encode::domain::{get_substitutions, DomainEncoder};
use crate::parse::Instance;
use crate::sat::Cnf;

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
    fn solve(&mut self) -> SolverResult;
}

/// Returns a solver for the given instance.
pub fn get_solver(inst: Instance) -> Result<Box<dyn Solver>, Error> {
    if inst.get_formula().is_conjunctive() {
        ConjunctiveSolver::new(inst).map(|s| Box::new(s) as Box<dyn Solver>)
    } else {
        Err(Error::unsupported("Non-conjuctive formula"))
    }
}

struct AbstractionSolver {
    instance: Instance,
    alphabet: IndexSet<char>,
    encoders: HashMap<Constraint, Box<dyn ConstraintEncoder>>,
    domain_encoder: DomainEncoder,
}

impl AbstractionSolver {}

impl Solver for AbstractionSolver {
    fn solve(&mut self) -> SolverResult {
        todo!()
    }
}

/// A solver for conjunctive formulas.
struct ConjunctiveSolver {
    instance: Instance,
    alphabet: IndexSet<char>,
    encoders: HashMap<Constraint, Box<dyn ConstraintEncoder>>,
    domain_encoder: DomainEncoder,
}

impl ConjunctiveSolver {
    fn inst_encoder(con: &Constraint) -> Box<dyn ConstraintEncoder> {
        match con {
            Constraint::WordEquation(eq) => Box::new(AlignmentEncoder::new(eq.clone())),
            Constraint::LinearConstraint(lc) => Box::new(MddEncoder::new(lc.clone())),
            Constraint::RegularConstraint(_) => todo!("Regular constraints are not supported"),
        }
    }

    fn new(instance: Instance) -> Result<Self, Error> {
        let mut alphabet = instance.get_formula().alphabet();

        alphabet.insert('a');

        let mut encoders = HashMap::new();

        if !instance.get_formula().is_conjunctive() {
            panic!("This solver only supports conjunctive formulas")
        }
        for a in instance.get_formula().asserted_atoms() {
            match a {
                Atom::Predicate(p) => {
                    let constraint = Constraint::from(p.clone());
                    let encoder = Self::inst_encoder(&constraint);
                    encoders.insert(constraint, encoder);
                }
                Atom::BoolVar(_) => todo!("Boolean variables are not supported"),
                Atom::True => (), // Do nothing
                Atom::False => todo!("Handle false atoms"),
            }
        }

        let dom_encoder = DomainEncoder::new(alphabet.clone());
        Ok(Self {
            instance,
            alphabet,
            encoders,
            domain_encoder: dom_encoder,
        })
    }

    fn encode_bounded(&mut self, bounds: &Bounds) -> EncodingResult {
        let mut encoding = EncodingResult::empty();
        if self.encoders.is_empty() {
            return EncodingResult::Trivial(true);
        }

        let mut bounds = bounds.clone();
        if self.encoders.len() == 1 {
            if let Some(Constraint::WordEquation(eq)) = self.encoders.keys().next() {
                bounds = sharpen_bounds(eq, &bounds, self.instance.get_var_manager())
            }
        }

        let ts = Instant::now();
        let subs_cnf = self
            .domain_encoder
            .encode(&bounds, self.instance.get_var_manager());
        log::debug!(
            "Encoded substitution in {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );
        encoding.join(subs_cnf);
        let dom = self.domain_encoder.encoding();
        for (_, enc) in self.encoders.iter_mut() {
            let res = enc.encode(&bounds, dom, self.instance.get_var_manager());
            encoding.join(res);
        }

        encoding
    }

    // Reset all states
    fn reset(&mut self) {
        self.domain_encoder = DomainEncoder::new(self.alphabet.clone());
        for (_, encoder) in self.encoders.iter_mut() {
            encoder.reset();
        }
    }
}

impl Solver for ConjunctiveSolver {
    fn solve(&mut self) -> SolverResult {
        let mut limit_upper_bounds =
            Bounds::infer(self.instance.get_formula(), self.instance.get_var_manager());
        log::info!("Found limit bounds: {}", limit_upper_bounds);
        // Make sure upper bounds for string variables are at least one, otherwise the encoding is not correct
        for v in self.instance.get_var_manager().of_sort(Sort::Int, true) {
            if self.instance.get_var_manager().is_lenght_var(v) {
                if let Some(0) = limit_upper_bounds.get(v).get_upper() {
                    log::info!("Setting upper bound for {} to 1", v);
                    limit_upper_bounds.set_upper(v, 1);
                }
            }
        }
        log::debug!("Adjusted limit bounds: {}", limit_upper_bounds);
        if limit_upper_bounds.any_empty() {
            log::info!("Empty upper bounds, unsat");
            return SolverResult::Unsat;
        }

        let mut current_bounds = Bounds::new();
        for v in self.instance.get_var_manager().of_sort(Sort::String, true) {
            let len_var = self.instance.get_var_manager().str_length_var(v).unwrap();
            current_bounds.set(
                len_var,
                IntDomain::Bounded(0, self.instance.get_start_bound() as isize),
            );
        }
        let mut effective_bounds = current_bounds.intersect(&limit_upper_bounds);

        log::info!(
            "Started solving loop for system of {} equations, alphabet size {}",
            self.instance.get_formula().num_atoms(),
            self.alphabet.len()
        );
        log::debug!("{}", self.instance.get_formula());

        let mut cadical: cadical::Solver = cadical::Solver::new();
        let mut time_encoding = 0;
        let mut time_solving = 0;
        let mut fm = Cnf::new();

        loop {
            log::info!("Current bounds {}", effective_bounds);
            if !effective_bounds.any_empty() {
                let ts = Instant::now();

                let encoding = self.encode_bounded(&effective_bounds);
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
                                    self.instance.get_var_manager(),
                                    &cadical,
                                ));
                                // Map variables that were removed in preprocessing to their default value
                                model.use_defaults();

                                log::info!(
                                    "Done. Total time encoding/solving: {}/{} ms",
                                    time_encoding,
                                    time_solving
                                );
                                return SolverResult::Sat(model);
                            }
                            Some(false) => {
                                if effective_bounds == limit_upper_bounds {
                                    // We reached the limit bounds, but did not find a solution.
                                    // This means no solution exists.
                                    // Return unsat
                                    log::info!("Reached limit bounds");
                                    return SolverResult::Unsat;
                                }
                                if self.encoders.values().any(|enc| !enc.is_incremental()) {
                                    // reset states if at least one solver is not incremental
                                    self.reset();
                                    cadical = cadical::Solver::new();
                                    log::debug!("Reset state");
                                }
                            }
                            None => panic!("SAT Solver returned unknown"),
                        }
                    }
                    EncodingResult::Trivial(false) => return SolverResult::Unsat,
                    EncodingResult::Trivial(true) => return SolverResult::Sat(Substitution::new()),
                }
            } else {
                log::info!("Empty bounds, skipping");
            }
            if let Some(upper) = self.instance.get_upper_bound() {
                if current_bounds.uppers_geq(upper as isize) {
                    // We reached the user-imposed upper bound and did not find a solution
                    // Return unknown
                    log::info!("Reached set upper bound");
                    return SolverResult::Unknown;
                }
            }

            current_bounds.next_square_uppers();
            if let Some(upper) = self.instance.get_upper_bound() {
                current_bounds.clamp_uppers(upper as isize);
            }
            effective_bounds = current_bounds.intersect(&limit_upper_bounds);
        }
    }
}

fn sharpen_bounds(eq: &WordEquation, bounds: &Bounds, vars: &VarManager) -> Bounds {
    let mut new_bounds = bounds.clone();
    // Todo: Cache this or do linearly
    let mut abs_consts: isize = 0;
    for c in eq.alphabet() {
        let rhs_c = eq.rhs().count(&Symbol::Constant(c)) as isize;
        let lhs_c = eq.lhs().count(&Symbol::Constant(c)) as isize;
        abs_consts += rhs_c - lhs_c;
    }

    for var_k in vars.of_sort(Sort::String, true) {
        let var_k_len = vars.str_length_var(var_k).unwrap();
        let denominator = eq.lhs().count(&Symbol::Variable(var_k.clone())) as isize
            - eq.rhs().count(&Symbol::Variable(var_k.clone())) as isize;
        if denominator == 0 {
            continue;
        }
        let mut abs_k: isize = 0;
        for var_j in vars.of_sort(Sort::String, true) {
            if var_j == var_k {
                continue;
            }
            let var_j_len = vars.str_length_var(var_j).unwrap();
            let abs_j = eq.lhs().count(&Symbol::Variable(var_j.clone())) as isize
                - eq.rhs().count(&Symbol::Variable(var_j.clone())) as isize;
            if abs_j * denominator < 0 {
                abs_k += abs_j * bounds.get_upper(var_j_len).unwrap();
            }
        }
        let sharpened = std::cmp::max((abs_consts - abs_k) / denominator, 0);
        if sharpened < bounds.get_upper(var_k_len).unwrap_or(isize::MAX) {
            new_bounds.set_upper(&var_k.len_var(), max(sharpened, 1));
        }
    }
    new_bounds
}
