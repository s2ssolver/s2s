use std::collections::HashSet;
use std::fs;
use std::io::Write;

use indexmap::IndexSet;

use std::time::Instant;

use crate::encode::{BindepEncoder, EncodingResult, VariableBounds};
use crate::encode::{IWoorpjeEncoder, WoorpjeEncoder, WordEquationEncoder};
use crate::formula::{Atom, ConstVal, Formula, Predicate, Substitution};
use crate::model::words::{Pattern, Symbol};
use crate::model::{words::WordEquation, Variable};

use crate::encode::substitution::SubstitutionEncoder;
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

/// Solver for a single word equation that uses a WordEquationEncoder to encode the instance.
struct EquationSolver<T: WordEquationEncoder> {
    equation: WordEquation,
    bounds: VariableBounds,
    max_bound: Option<usize>,
    encoder: T,
    subs_encoder: SubstitutionEncoder,
}

impl<T: WordEquationEncoder> EquationSolver<T> {
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

    /// Create a new Woorpje solver for the given instance.
    /// Returns an error if the instance is not a single word equation.
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let eq = match instance.get_formula() {
            Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => Ok(eq.clone()),
            Formula::False => {
                let mut lhs = Pattern::empty();
                lhs.append(&Symbol::Constant('a'));
                Ok(WordEquation::new(lhs, Pattern::empty()))
            }
            Formula::True => Ok(WordEquation::empty()),
            _ => Err(format!(
                "Instance is not a single word equation but {:?}",
                instance.get_formula()
            )),
        }?;
        let subs_encoder = SubstitutionEncoder::new(eq.alphabet(), eq.variables());
        Ok(Self {
            encoder: T::new(eq.clone()),
            equation: eq,
            bounds: VariableBounds::new(instance.get_lower_bound()),
            max_bound: instance.get_upper_bound(),
            subs_encoder,
        })
    }

    fn encode_bounded(&mut self) -> EncodingResult {
        let bounds = sharpen_bounds(&self.equation, &self.bounds, &self.equation.variables());
        log::debug!("Sharpened bounds: {:?}", bounds);

        let mut encoding = EncodingResult::empty();

        let ts = Instant::now();
        let subs_cnf = self.subs_encoder.encode(&bounds);
        log::debug!(
            "Encoded substitution in {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );
        encoding.join(subs_cnf);
        let sub_encoding = self.subs_encoder.get_encoding().unwrap();
        encoding.join(self.encoder.encode(&bounds, sub_encoding));
        encoding
    }

    // Reset all states
    fn reset(&mut self) {
        self.subs_encoder =
            SubstitutionEncoder::new(self.equation.alphabet(), self.equation.variables());
        self.encoder.reset();
    }
}

impl<T: WordEquationEncoder> Solver for EquationSolver<T> {
    fn solve(&mut self) -> SolverResult {
        log::info!("Started solving loop for equation {}", self.equation);
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

                    /*fm.shuffle(&mut thread_rng());
                    cadical = cadical::Solver::new();
                    fm.iter()
                        .for_each(|clause| cadical.add_clause(clause.clone()));*/

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
                        match &self.subs_encoder.get_encoding() {
                            Some(sub_encoding) => {
                                for (v, s) in sub_encoding.get_substitutions(&cadical) {
                                    model.set(&v, ConstVal::String(s.clone()));
                                }
                            }
                            _ => panic!("No substitution encoding found"),
                        };
                        log::info!(
                            "Done. Total time encoding/solving: {}/{} ms",
                            time_encoding,
                            time_solving
                        );
                        return SolverResult::Sat(model);
                    } else if !self.encoder.is_incremental() {
                        // reset states if solver is not incremental
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
            if !self.bounds.next_square(self.max_bound) {
                break;
            }
        }
        SolverResult::Unsat
    }
}

pub struct EquationSystemSolver<T: WordEquationEncoder> {
    equations: Vec<WordEquation>,
    bounds: VariableBounds,
    alphabet: IndexSet<char>,
    variables: IndexSet<Variable>,
    max_bound: Option<usize>,
    encoder: Vec<T>,
    subs_encoder: SubstitutionEncoder,
}

impl<T: WordEquationEncoder> EquationSystemSolver<T> {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let mut eqs = Vec::new();
        let mut alphabet = IndexSet::new();
        let mut variables = IndexSet::new();

        match instance.get_formula() {
            Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => {
                eqs.push(eq.clone());
                alphabet.extend(eq.alphabet().iter().cloned());
                variables.extend(eq.variables().iter().cloned());
            }
            Formula::And(fs) => {
                for f in fs {
                    match f {
                        Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => {
                            eqs.push(eq.clone());
                            alphabet.extend(eq.alphabet().iter().cloned());
                            variables.extend(eq.variables().iter().cloned());
                        }
                        _ => return Err(format!("Instance is not a system of word equations")),
                    }
                }
            }
            _ => return Err(format!("Instance is not a system of word equations")),
        }

        let subs_encoder = SubstitutionEncoder::new(alphabet.clone(), variables.clone());
        let mut encoders = Vec::new();
        for eq in &eqs {
            encoders.push(T::new(eq.clone()));
        }
        Ok(Self {
            encoder: encoders,
            equations: eqs,
            alphabet,
            variables,
            bounds: VariableBounds::new(instance.get_lower_bound()),
            max_bound: instance.get_upper_bound(),
            subs_encoder,
        })
    }

    fn encode_bounded(&mut self) -> EncodingResult {
        let mut encoding = EncodingResult::empty();

        let ts = Instant::now();
        let subs_cnf = self.subs_encoder.encode(&self.bounds);
        log::debug!(
            "Encoded substitution in {} clauses ({} ms)",
            subs_cnf.clauses(),
            ts.elapsed().as_millis()
        );
        encoding.join(subs_cnf);
        let sub_encoding = self.subs_encoder.get_encoding().unwrap();
        for enc in self.encoder.as_mut_slice() {
            let res = enc.encode(&self.bounds, sub_encoding);
            encoding.join(res);
        }

        encoding
    }

    // Reset all states
    fn reset(&mut self) {
        self.subs_encoder = SubstitutionEncoder::new(self.alphabet.clone(), self.variables.clone());
        for encoder in self.encoder.as_mut_slice() {
            encoder.reset();
        }
    }
}

impl<T: WordEquationEncoder> Solver for EquationSystemSolver<T> {
    fn solve(&mut self) -> SolverResult {
        log::info!(
            "Started solving loop for system of {} equations",
            self.equations.len()
        );
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
                        match &self.subs_encoder.get_encoding() {
                            Some(sub_encoding) => {
                                for (v, s) in sub_encoding.get_substitutions(&cadical) {
                                    model.set(&v, ConstVal::String(s.clone()));
                                }
                            }
                            _ => panic!("No substitution encoding found"),
                        };
                        log::info!(
                            "Done. Total time encoding/solving: {}/{} ms",
                            time_encoding,
                            time_solving
                        );
                        return SolverResult::Sat(model);
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
            if !self.bounds.next_square(self.max_bound) {
                break;
            }
        }
        SolverResult::Unsat
    }
}

fn sharpen_bounds(
    eq: &WordEquation,
    bounds: &VariableBounds,
    vars: &IndexSet<Variable>,
) -> VariableBounds {
    let mut new_bounds = bounds.clone();
    // Todo: Cache this or do linearly
    let mut abs_consts: isize = 0;
    for c in eq.alphabet() {
        let rhs_c = eq.rhs().count(&Symbol::Constant(c)) as isize;
        let lhs_c = eq.lhs().count(&Symbol::Constant(c)) as isize;
        abs_consts += rhs_c - lhs_c;
    }

    for var_k in vars {
        let denominator = eq.lhs().count(&Symbol::Variable(var_k.clone())) as isize
            - eq.rhs().count(&Symbol::Variable(var_k.clone())) as isize;
        if denominator == 0 {
            continue;
        }
        let mut abs_k: isize = 0;
        for var_j in vars {
            if var_j == var_k {
                continue;
            }
            let abs_j = eq.lhs().count(&Symbol::Variable(var_j.clone())) as isize
                - eq.rhs().count(&Symbol::Variable(var_j.clone())) as isize;
            if abs_j * denominator < 0 {
                abs_k += abs_j * bounds.get(var_j) as isize;
            }
        }
        let sharpened = std::cmp::max((abs_consts - abs_k) / denominator, 0) as usize;
        if sharpened < bounds.get(var_k) {
            new_bounds.set(var_k, sharpened);
        }
    }
    new_bounds
}

/// The Woorpje solver for word equations.
/// This solver uses a SAT solver to check whether a word equation is satisfiable.
/// Can only solver instances with a single word equation.
pub struct Woorpje {
    solver: EquationSystemSolver<WoorpjeEncoder>,
}

impl Solver for Woorpje {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl Woorpje {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}

/// The incremental extension of the Woorpje solver for word equations.
/// Can only solver instances with a single word equation.
pub struct IWoorpje {
    solver: EquationSystemSolver<IWoorpjeEncoder>,
}

impl Solver for IWoorpje {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl IWoorpje {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}

pub struct Bindep {
    solver: EquationSystemSolver<BindepEncoder>,
}

impl Solver for Bindep {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl Bindep {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let solver = EquationSystemSolver::new(instance)?;
        Ok(Self { solver })
    }
}
