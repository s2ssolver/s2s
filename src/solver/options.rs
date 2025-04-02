use crate::interval::Interval;

use super::refine::BoundStep;

const DEFAULT_SIMPLIFY: bool = true;
const DEFAULT_PREPROCESS_PASSES: usize = 20;
const DEFAULT_CHECK_MODEL: bool = false;
const DEFAULT_UNSAT_ON_MAX_BOUND: bool = false;
const DEFAULT_MAX_BLOCKING: usize = 100;
const DEFAULT_GET_MODEL: bool = false;

#[derive(Debug, Clone)]
pub struct SolverOptions {
    pub dry: bool,
    pub simplify: bool,
    /// The number of extra preprocessing passes allowed.
    /// An extra preprocessing pass is performed if the size of the formula did not decrease in previous pass.
    /// If set to 0, will only apply preprocessing while the size of the formula is decreasing.
    pub preprocess_extra_passes: usize,

    pub max_bounds: Interval,
    pub step: BoundStep,
    pub check_model: bool,
    /// Wheter to print the model after solving.
    /// This is only used if the solver returns `sat`.
    pub get_model: bool,
    pub unsat_on_max_bound: bool,
    pub init_upper_bound: i32,
    pub print_preprocessed: bool,

    /// The maximum number of blocking assignments the over-approximation before returning `unknown`.
    pub max_blocking: usize,
}
impl Default for SolverOptions {
    fn default() -> Self {
        Self {
            dry: false,
            simplify: DEFAULT_SIMPLIFY,
            preprocess_extra_passes: DEFAULT_PREPROCESS_PASSES,
            max_bounds: Interval::unbounded(),
            step: BoundStep::default(),
            check_model: DEFAULT_CHECK_MODEL,
            get_model: DEFAULT_GET_MODEL,
            unsat_on_max_bound: DEFAULT_UNSAT_ON_MAX_BOUND,
            init_upper_bound: 2,
            max_blocking: DEFAULT_MAX_BLOCKING,
            print_preprocessed: false,
        }
    }
}

impl SolverOptions {
    /// Whether to use a dry-run mode.
    /// In dry-run mode, the solver does not actually solve the instance, but only preprocesses it.
    /// If after preprcessing the formula is not trivially sat/unsat, the solver returns `Unknown`.
    pub fn dry(&mut self, dry: bool) -> &mut Self {
        self.dry = dry;
        self
    }

    /// Whether to simplify the formula before solving it.
    /// Simplification is done by applying algebraic simplifications to the formula.
    pub fn simplify(&mut self, simplify: bool) -> &mut Self {
        self.simplify = simplify;
        self
    }

    /// The maximum upper bound the solver will try to find a solution for.
    /// If no solution is found within this bound, the solver returns `unknown`.
    /// Use `unsat_on_max_bound` to change this behavior to return `unsat` instead.
    pub fn max_bounds(&mut self, max_bounds: u32) -> &mut Self {
        self.max_bounds = Interval::bounded_above(max_bounds);
        self
    }

    /// If a maximum bound is set (using [`max_bounds`](Self::max_bounds)), the solver will return `unsat` instead of `unknown` if the maximum bound is reached.
    pub fn unsat_on_max_bound(&mut self, unsat_on_max_bound: bool) -> &mut Self {
        self.unsat_on_max_bound = unsat_on_max_bound;
        self
    }

    /// The initial upper bound for the variables.
    /// This bounds is used to initialize the upper bounds for the variables for the first round of solving.
    pub fn init_upper_bound(&mut self, init_upper_bound: i32) -> &mut Self {
        self.init_upper_bound = init_upper_bound;
        self
    }

    /// Prints the preprocessed formula in SMT-LIB format.
    pub fn print_preprocessed(&mut self) -> &mut Self {
        self.print_preprocessed = true;
        self
    }
}
