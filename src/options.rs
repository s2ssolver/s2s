use crate::{interval::Interval, BoundStep};

const DEFAULT_SIMPLIFY: bool = true;
const DEFAULT_PREPROCESS_PASSES: usize = 20;
const DEFAULT_UNSAT_ON_MAX_BOUND: bool = false;
const DEFAULT_MAX_BLOCKING: usize = 100;
const DEFAULT_GET_MODEL: bool = false;
const DEFAULT_MAX_BOOL_GUESS: usize = 10;
const DEFAULT_GUESS_BOOLS: bool = true;
const DEFAULT_COMPRESSION: bool = true;
const DEFAULT_CEGAR: bool = true;

#[derive(Debug, Clone)]
pub struct Options {
    /// Whether to use a dry-run mode.
    /// In dry-run mode, the solver does not actually solve the instance, but only preprocesses it.
    /// If after preprcessing the formula is not trivially sat/unsat, the solver returns `Unknown`.
    pub dry: bool,
    /// Whether to simplify the formula before solving it.
    /// Simplification is done by applying algebraic simplifications to the formula.
    pub simplify: bool,
    /// The maximum number of simplifcation passes during preprocessing.
    /// This is a soft limit, the simplifier might choose do perform more passes if necessery.
    /// Moreover, the simplifcation procedure might be called more than once.
    pub simp_max_passes: usize,
    /// The maximum upper bound the solver will try to find a solution for.
    /// If no solution is found within this bound, the solver returns `unknown`.
    /// Use `unsat_on_max_bound` to change this behavior to return `unsat` instead.
    pub max_bounds: Interval,
    /// The step size by which bounds are increased on unsat
    pub step: BoundStep,
    /// If `true` solves over approximations and gradually encodes more literals if a counter-exmample is found
    /// If `false` will directly encode all literals in the formula.
    pub cegar: bool,
    /// Wheter to print the model after solving.
    /// This is only used if the solver returns `sat`.
    pub get_model: bool,
    /// If a maximum bound is set (using [`max_bounds`](Self::max_bounds)), the solver will return `unsat` instead of `unknown` if the maximum bound is reached.
    pub unsat_on_max_bound: bool,
    /// The initial upper bound for the variables.
    /// This bounds is used to initialize the upper bounds for the variables for the first round of solving.
    /// This is soft bound, the solver might choose to use larger bounds.
    pub init_upper_bound: i32,
    /// Prints the preprocessed formula in SMT-LIB format.
    pub print_preprocessed: bool,

    /// Whether to guess the value of Boolean variables during prepreocessing.
    pub guess_bools: bool,
    /// The maximum number of Boolean variables to guess a value for.
    pub max_bool_guesses: usize,

    /// Whether to perform the range-compressions
    pub compress: bool,

    /// The maximum number of blocking assignments the over-approximation before returning `unknown`.
    pub max_blocking: usize,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            dry: false,
            simplify: DEFAULT_SIMPLIFY,
            simp_max_passes: DEFAULT_PREPROCESS_PASSES,
            max_bounds: Interval::unbounded(),
            step: BoundStep::default(),
            guess_bools: DEFAULT_GUESS_BOOLS,
            get_model: DEFAULT_GET_MODEL,
            unsat_on_max_bound: DEFAULT_UNSAT_ON_MAX_BOUND,
            init_upper_bound: 1,
            max_blocking: DEFAULT_MAX_BLOCKING,
            print_preprocessed: false,
            max_bool_guesses: DEFAULT_MAX_BOOL_GUESS,
            compress: DEFAULT_COMPRESSION,
            cegar: DEFAULT_CEGAR,
        }
    }
}

impl Options {
    pub fn set_max_bound(&mut self, b: u16) {
        self.max_bounds = Interval::new(-(b as i32), b as i32)
    }
}
