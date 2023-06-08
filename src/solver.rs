use std::collections::HashMap;

use indexmap::IndexSet;

use std::time::Instant;

use crate::bounds::{Bounds, IntDomain};
use crate::encode::{
    BindepEncoder, EncodingResult, IntegerDomainBounds, MddEncoder, PredicateEncoder,
    WordEquationEncoder,
};

use crate::formula::{Atom, ConstVal, Formula, Predicate, Substitution};
use crate::model::words::Symbol;
use crate::model::words::WordEquation;
use crate::model::{Sort, VarManager};

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

pub struct ConjunctiveSolver {
    instance: Instance,
    alphabet: IndexSet<char>,
    encoders: HashMap<Predicate, Box<dyn PredicateEncoder>>,
    domain_encoder: DomainEncoder,
}

impl ConjunctiveSolver {
    fn inst_encoder(predicate: &Predicate) -> Box<dyn PredicateEncoder> {
        match predicate {
            Predicate::WordEquation(eq) => Box::new(BindepEncoder::new(eq.clone())),
            Predicate::RegulaConstraint(_, _) => todo!(),
            Predicate::LinearConstraint(lc) => Box::new(MddEncoder::new(lc.clone())),
        }
    }

    pub fn new(instance: Instance) -> Result<Self, String> {
        let alphabet = instance.get_formula().alphabet();
        let mut encoders = HashMap::new();

        let non_conjunctive_error = Err(format!(
            "Instance is not a conjunctive formula: {}",
            instance.get_formula()
        ));
        match instance.get_formula() {
            Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => {
                encoders.insert(
                    Predicate::WordEquation(eq.clone()),
                    Self::inst_encoder(&Predicate::WordEquation(eq.clone())),
                );
            }
            Formula::And(fs) => {
                for f in fs {
                    match f {
                        Formula::Atom(Atom::Predicate(p)) => {
                            encoders.insert(p.clone(), Self::inst_encoder(p));
                        }
                        _ => return non_conjunctive_error,
                    }
                }
            }
            _ => return non_conjunctive_error,
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
        let bounds = if let Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) =
            self.instance.get_formula()
        {
            sharpen_bounds(eq, &bounds, self.instance.get_var_manager())
        } else {
            bounds.clone()
        };

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
        let limit_upper_bounds =
            Bounds::infer(self.instance.get_formula(), self.instance.get_var_manager());
        log::info!("Found limit bounds: {}", limit_upper_bounds);
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
            "Started solving loop for system of {} equations",
            self.instance.get_formula().num_atoms()
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
                        if let Some(true) = res {
                            let mut model = Substitution::with_defaults();
                            for (v, s) in get_substitutions(
                                self.domain_encoder.encoding(),
                                self.instance.get_var_manager(),
                                &cadical,
                            ) {
                                model.set(&v, ConstVal::String(s.clone()));
                            }
                            log::info!(
                                "Done. Total time encoding/solving: {}/{} ms",
                                time_encoding,
                                time_solving
                            );
                            return SolverResult::Sat(model);
                        } else if self.encoders.values().any(|enc| !enc.is_incremental()) {
                            // reset states if at least one solver is not incremental
                            self.reset();
                            cadical = cadical::Solver::new();
                            log::debug!("Reset state");
                        }
                    }
                    EncodingResult::Trivial(false) => return SolverResult::Unsat,
                    EncodingResult::Trivial(true) => {
                        return SolverResult::Sat(Substitution::with_defaults())
                    }
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
            new_bounds.set_upper(&var_k.len_var(), sharpened);
        }
    }
    new_bounds
}
