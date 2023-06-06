use std::collections::HashSet;
use std::fs;
use std::io::Write;

use indexmap::IndexSet;

use std::time::Instant;

use crate::encode::{BindepEncoder, EncodingResult, IntegerDomainBounds};
use crate::encode::{IWoorpjeEncoder, WoorpjeEncoder, WordEquationEncoder};
use crate::formula::{Atom, ConstVal, Formula, Predicate, Substitution};
use crate::model::words::Symbol;
use crate::model::words::WordEquation;
use crate::model::{Sort, VarManager};

use crate::encode::domain::{get_substitutions, DomainEncoder};
use crate::parse::Instance;
use crate::sat::{Cnf, PLit};

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

pub struct EquationSystemSolver<'a, T: WordEquationEncoder> {
    equations: Vec<WordEquation>,
    bounds: IntegerDomainBounds,
    alphabet: IndexSet<char>,
    var_manager: &'a VarManager,
    max_bound: Option<usize>,
    encoder: Vec<T>,
    dom_encoder: DomainEncoder<'a>,
}

// TODO:
// - The solver should take ownership of the Instance and provide a way to access it from outside. Right now the lifetime of the solver is bound to the lifetime of the instance, which requires a lot of lifetime annotations.

impl<'a, T: WordEquationEncoder> EquationSystemSolver<'a, T> {
    pub fn new(instance: &'a Instance) -> Result<Self, String> {
        let mut eqs = Vec::new();
        let mut alphabet = IndexSet::new();

        match instance.get_formula() {
            Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => {
                eqs.push(eq.clone());
                alphabet.extend(eq.alphabet().iter().cloned());
            }
            Formula::And(fs) => {
                for f in fs {
                    match f {
                        Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => {
                            eqs.push(eq.clone());
                            alphabet.extend(eq.alphabet().iter().cloned());
                        }
                        _ => return Err("Instance is not a system of word equations".to_string()),
                    }
                }
            }
            _ => return Err("Instance is not a system of word equations".to_string()),
        }

        let dom_encoder = DomainEncoder::new(alphabet.clone(), instance.get_var_manager());
        let encoders = Vec::new();

        Ok(Self {
            encoder: encoders,
            equations: eqs,
            alphabet,
            var_manager: instance.get_var_manager(),
            bounds: IntegerDomainBounds::new((0, instance.get_lower_bound() as isize)),
            max_bound: instance.get_upper_bound(),
            dom_encoder,
        })
    }

    #[allow(unused)]
    pub fn write_dimacs(&self, clauses: &Cnf, assms: Vec<PLit>) {
        let num_clauses = clauses.len() + assms.len();
        let mut vars = HashSet::new();
        for clause in clauses {
            for lit in clause {
                vars.insert(lit.abs());
            }
        }
        for a in &assms {
            vars.insert(a.abs());
        }
        let num_vars = vars.len();

        let mut f = fs::File::options()
            .create(true)
            .write(true)
            .truncate(true)
            .open(".local/fm.dimacs")
            .unwrap();

        f.write_fmt(format_args!("p cnf {} {}\n", num_vars, num_clauses))
            .unwrap();
        for clause in clauses {
            for lit in clause {
                f.write_fmt(format_args!("{} ", lit)).unwrap();
            }
            f.write_fmt(format_args!("0\n")).unwrap();
        }

        for a in assms {
            f.write_fmt(format_args!("{} 0\n", a)).unwrap();
        }
    }

    fn encode_bounded(&mut self) -> EncodingResult {
        let mut encoding = EncodingResult::empty();
        let bounds = if self.equations.len() == 1 {
            sharpen_bounds(
                self.equations.first().unwrap(),
                &self.bounds,
                self.var_manager,
            )
        } else {
            self.bounds.clone()
        };

        let ts = Instant::now();
        let subs_cnf = self.dom_encoder.encode(&bounds);
        log::debug!(
            "Encoded substitution in {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );
        encoding.join(subs_cnf);
        let dom = self.dom_encoder.encoding();
        for enc in self.encoder.as_mut_slice() {
            let res = enc.encode(&bounds, dom, self.var_manager);
            encoding.join(res);
        }

        encoding
    }

    // Reset all states
    fn reset(&mut self) {
        self.dom_encoder = DomainEncoder::new(self.alphabet.clone(), self.var_manager);
        for encoder in self.encoder.as_mut_slice() {
            encoder.reset();
        }
    }
}

impl<'a, T: WordEquationEncoder> Solver for EquationSystemSolver<'a, T> {
    fn solve(&mut self) -> SolverResult {
        log::info!(
            "Started solving loop for system of {} equations",
            self.equations.len()
        );
        let mut mut_waitlist = IndexSet::new();
        for eq in self.equations.iter() {
            mut_waitlist.insert(eq.clone());
        }
        // Just add one encoder
        self.encoder.push(T::new(mut_waitlist.pop().unwrap()));
        let mut cadical: cadical::Solver = cadical::Solver::new();
        let mut time_encoding = 0;
        let mut time_solving = 0;
        let mut fm = Cnf::new();

        loop {
            log::info!("Current bounds {}", self.bounds);
            let ts = Instant::now();
            let encoding = self.encode_bounded();
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
                            self.dom_encoder.encoding(),
                            self.var_manager,
                            &cadical,
                        ) {
                            model.set(&v, ConstVal::String(s.clone()));
                        }
                        // Check which equations in the waitlist are not satisfied by the model, add them to the encoding
                        let mut to_add = Vec::new();
                        for eq in &mut_waitlist {
                            match eq.is_solution(&model) {
                                None | Some(false) => {
                                    to_add.push(eq.clone());
                                }
                                _ => {}
                            }
                        }

                        if to_add.is_empty() {
                            log::info!(
                                "Done. Total time encoding/solving: {}/{} ms",
                                time_encoding,
                                time_solving
                            );
                            return SolverResult::Sat(model);
                        } else {
                            // Add some of the equations that were not satisfied to the found model
                            log::info!(
                                "{} out of {} ignored equations were not satisfied, adding {} equations to the model",
                                to_add.len(),
                                mut_waitlist.len(),
                                to_add.len().min(3)
                            );
                            for eq in &to_add[0..2] {
                                mut_waitlist.remove(eq);
                                self.encoder.push(T::new(eq.clone()));
                            }
                        }
                    } else if self.encoder.iter().any(|enc| !enc.is_incremental()) {
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
            if !self.bounds.next_square(self.max_bound.map(|v| v as isize)) {
                break;
            }
        }
        SolverResult::Unsat
    }
}

fn sharpen_bounds(
    eq: &WordEquation,
    bounds: &IntegerDomainBounds,
    vars: &VarManager,
) -> IntegerDomainBounds {
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
                abs_k += abs_j * bounds.get_upper(var_j_len);
            }
        }
        let sharpened = std::cmp::max((abs_consts - abs_k) / denominator, 0);
        if sharpened < bounds.get_upper(var_k_len) {
            new_bounds.set_upper(&var_k.len_var(), sharpened);
        }
    }
    new_bounds
}

/// The Woorpje solver for word equations.
/// This solver uses a SAT solver to check whether a word equation is satisfiable.
/// Can only solver instances with a single word equation.
pub struct Woorpje<'a> {
    solver: EquationSystemSolver<'a, WoorpjeEncoder>,
}

impl<'a> Solver for Woorpje<'a> {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl<'a> Woorpje<'a> {
    pub fn new(instance: &'a Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}

/// The incremental extension of the Woorpje solver for word equations.
/// Can only solver instances with a single word equation.
pub struct IWoorpje<'a> {
    solver: EquationSystemSolver<'a, IWoorpjeEncoder>,
}

impl<'a> Solver for IWoorpje<'a> {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl<'a> IWoorpje<'a> {
    pub fn new(instance: &'a Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}

pub struct Bindep<'a> {
    solver: EquationSystemSolver<'a, BindepEncoder>,
}

impl<'a> Solver for Bindep<'a> {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl<'a> Bindep<'a> {
    pub fn new(instance: &'a Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}
