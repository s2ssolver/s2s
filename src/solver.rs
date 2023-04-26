use std::collections::{HashMap, HashSet};

use std::fmt::Display;
use std::time::Instant;

use crate::encode::{EncodingResult, VariableBounds};
use crate::encode::{IWoorpjeEncoder, WoorpjeEncoder, WordEquationEncoder};
use crate::formula::{Atom, Formula, Predicate};
use crate::model::words::{Pattern, Symbol};
use crate::model::{words::WordEquation, Variable};

use crate::encode::substitution::SubstitutionEncoder;
/// A problem instance, consisting of a formula and a set of variables
/// Should be created using the `parse` module
#[derive(Clone, Debug)]
pub struct Instance {
    /// The formula to solve
    formula: Formula,
    /// The set of all variables
    vars: HashSet<Variable>,
    /// The maximum bound for any variable to check.
    /// If `None`, no bound is set, which will might in an infinite search if the instance is not satisfiable.
    /// If `Some(n)`, the solver will only check for a solution with a bound of `n`.
    /// If no solution is found with every variable bound to `n`, the solver will return `Unsat`.
    ubound: Option<usize>,
}

impl Instance {
    pub fn new(formula: Formula, vars: HashSet<Variable>) -> Self {
        Instance {
            formula,
            vars,
            ubound: None,
        }
    }

    pub fn set_bound(&mut self, bound: usize) {
        self.ubound = Some(bound);
    }

    pub fn set_formula(&mut self, formula: Formula) {
        self.formula = formula;
    }

    pub fn remove_bound(&mut self) {
        self.ubound = None;
    }

    pub fn get_formula(&self) -> &Formula {
        &self.formula
    }

    pub fn get_vars(&self) -> &HashSet<Variable> {
        &self.vars
    }
}

/// The result of a satisfiability check
pub enum SolverResult {
    /// The instance is satisfiable with the given model
    Sat(HashMap<Variable, String>),
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
    pub fn get_model(&self) -> Option<&HashMap<Variable, String>> {
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
    /// Create a new Woorpje solver for the given instance.
    /// Returns an error if the instance is not a single word equation.
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let eq = match &instance.formula {
            Formula::Atom(Atom::Predicate(Predicate::WordEquation(eq))) => Ok(eq.clone()),
            Formula::False => {
                let mut lhs = Pattern::empty();
                lhs.append(&Symbol::Constant('a'));
                Ok(WordEquation::new(lhs, Pattern::empty()))
            }
            Formula::True => Ok(WordEquation::empty()),
            _ => Err("Instance is not a single word equation".to_string()),
        }?;
        let subs_encoder = SubstitutionEncoder::new(eq.alphabet(), eq.variables());
        Ok(Self {
            encoder: T::new(eq.clone()),
            equation: eq,
            bounds: VariableBounds::new(1),
            max_bound: instance.ubound,
            subs_encoder,
        })
    }
}

impl<T: WordEquationEncoder> EquationSolver<T> {
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
                        let solution = match &self.subs_encoder.get_encoding() {
                            Some(sub_encoding) => sub_encoding.get_substitutions(&cadical),
                            None => HashMap::new(),
                        };
                        log::info!(
                            "Done. Total time encoding/solving: {}/{} ms",
                            time_encoding,
                            time_solving
                        );
                        return SolverResult::Sat(solution);
                    } else {
                        if !self.encoder.is_incremental() {
                            // reset states if solver is not incremental
                            self.reset();
                            cadical = cadical::Solver::new();
                            log::debug!("Reset state");
                        }
                    }
                }
                EncodingResult::Trivial(false) => return SolverResult::Unsat,
                EncodingResult::Trivial(true) => return SolverResult::Sat(HashMap::new()),
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
    vars: &HashSet<Variable>,
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
    solver: EquationSolver<WoorpjeEncoder>,
}

impl Solver for Woorpje {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl Woorpje {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let solver = EquationSolver::new(instance)?;
        Ok(Self { solver })
    }
}

/// The incremental extension of the Woorpje solver for word equations.
/// Can only solver instances with a single word equation.
pub struct IWoorpje {
    solver: EquationSolver<IWoorpjeEncoder>,
}

impl Solver for IWoorpje {
    fn solve(&mut self) -> SolverResult {
        self.solver.solve()
    }
}

impl IWoorpje {
    pub fn new(instance: &Instance) -> Result<Self, String> {
        let solver = EquationSolver::new(instance)?;
        Ok(Self { solver })
    }
}
