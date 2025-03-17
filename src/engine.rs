use std::time::Instant;

use indexmap::IndexSet;
use regulaer::re::{ReOp, Regex};

use crate::{
    abstraction::{build_abstraction, LitDefinition},
    alphabet,
    bounds::{BoundInferer, InferringStrategy, LinearRefiner},
    domain::Domain,
    interval::Interval,
    node::{
        canonical::{
            ArithOperator, Assignment, AtomKind, LinearArithTerm, LinearConstraint, Literal,
            WordEquation,
        },
        get_entailed_literals,
        normal::to_nnf,
        smt::to_script,
        Node, NodeKind, NodeManager, Sort, Sorted, VarSubstitution,
    },
    preprocess::{canonicalize, compress_ranges, Preprocessor},
    solver::Solver,
    SolverAnswer, SolverOptions,
};

use crate::error::PublicError as Error;

/// The main engine.
/// The engine is the entry point for the solver.
/// It takes a series of formulas and checks their satisfiability.
/// The engine responsible for preprocessing and solving the formulas.
pub struct Engine {
    options: SolverOptions,

    /// The newly asserted formulas for the next satisfiability check.
    /// When `check` is called, the the solver will check the satisfiability of the conjunction of all assertions.
    /// Note that the solver currently is not incremental.
    /// That is, after a call to `check`, the assertions are cleared.
    assertions: Vec<Node>,

    /// The result of the last satisfiability check.
    /// Prior to the first call to `check`, the result is `Sat`.
    result: SolverAnswer,
}

impl Engine {
    pub fn with_options(options: SolverOptions) -> Self {
        Self {
            options,
            result: SolverAnswer::Sat(None), // trivially sat
            assertions: Vec::new(),
        }
    }

    /// Asserts a formula for the next satisfiability check.
    /// Calling `check` will check the satisfiability of the conjunction of all assertions.
    /// After the check, the assertions are cleared.
    pub fn assert(&mut self, fm: &Node) {
        self.assertions.push(fm.clone());
    }

    /// Solves the formula that has been asserted so far.
    /// Returns the result of the satisfiability check.
    pub fn check(&mut self, mngr: &mut NodeManager) -> Result<(), Error> {
        // Pop all assertions and build the formula
        let fm = mngr.and(self.assertions.drain(..).collect());

        // Preprocess the formula
        let (fm, subst) = self.preprocess(&fm, mngr)?;

        // Solve the formula
        let res = match self.solve(&fm, mngr)? {
            SolverAnswer::Sat(Some(model)) => {
                // If SAT, apply the substitutions from preprocessing to the model
                let model = subst.compose(model, mngr);
                SolverAnswer::Sat(Some(model))
            }
            SolverAnswer::Sat(None) => SolverAnswer::Sat(Some(subst)),
            SolverAnswer::Unsat => SolverAnswer::Unsat,
            SolverAnswer::Unknown => SolverAnswer::Unknown,
        };

        // Store the result
        self.result = res;
        Ok(())
    }

    /// Returns the result of the last satisfiability check.
    pub fn get_result(&self) -> &SolverAnswer {
        &self.result
    }

    /// Preprocess the given formula.
    /// This function applies a series of simplifications and rewrites to the formula.
    /// After that, it canonicalizes the formula. The resulting canonical formula is understood by the solver.
    /// If the preprocessed formula has a model, then the substitutions can be applied to the model to get a solution for the original formula.
    /// This is called before the main solving loop.
    fn preprocess(
        &mut self,
        fm: &Node,
        mngr: &mut NodeManager,
    ) -> Result<(Node, VarSubstitution), Error> {
        // Preprocess

        let nnf = to_nnf(fm, mngr);

        let mut preprocessor = Preprocessor::default();

        let simped = if self.options.simplify {
            preprocessor.apply(&nnf, self.options.preprocess_extra_passes, mngr)?
        } else {
            nnf
        };

        // These are the substitutions applied by the preprocessor
        // We need to store them and re-apply them to the model of the preprocessed formula, to get the model of the original formula
        let prepr_subst = preprocessor.applied_substitutions().clone();

        // Compress the char ranges
        let t = Instant::now();
        let compressed = compress_ranges(&simped, mngr);

        log::debug!("Compressed formula in {:?}", t.elapsed());
        log::debug!("Compressed formula: {}", compressed);

        // If the 'print_preprocessed' option is set, print the preprocessed formula
        if self.options.print_preprocessed {
            println!("{}", to_script(&compressed));
        }

        // Canonicalize.
        // This brings the formula into a normal that the solver understands.
        let canonical = canonicalize(&compressed, mngr);
        log::debug!("Canonicalized formula: {}", canonical);

        Ok((canonical, prepr_subst))
    }

    /// Solves the given formula in canonical form.
    fn solve(&mut self, fm: &Node, mngr: &mut NodeManager) -> Result<SolverAnswer, Error> {
        // Early return if the formula is trivially sat/unsat
        if let NodeKind::Bool(v) = *fm.kind() {
            return Ok(if v {
                SolverAnswer::Sat(Some(VarSubstitution::default()))
            } else {
                SolverAnswer::Unsat
            });
        }

        // Infer alphabet
        let alphabet = alphabet::infer(&fm);
        log::info!("Inferred alphabet of size {}", alphabet.len(),);
        log::debug!("Alphabet: {}", alphabet);

        // Build abstraction
        let abstraction = build_abstraction(&fm)?;

        // Initialize domain for all variables
        let init_dom = match self.init_domain_approx(&fm, mngr) {
            Some(bs) => bs,
            None => {
                log::info!("No valid initial bounds. Unsat.");
                return Ok(SolverAnswer::Unsat);
            }
        };

        // Initialize the solver
        // Initially, it only knows the skeleton and the alphabet.
        let solver = Solver::new(
            self.options.clone(),
            abstraction.skeleton().clone(),
            alphabet,
            init_dom,
        );

        if self.options.dry {
            return Ok(SolverAnswer::Unknown);
        }

        // Start over-approximation loop
        self.solve_cegar(
            fm.clone(),
            solver,
            abstraction.definitions().cloned().collect(),
            mngr,
        )
    }

    /// The CEGAR solving loop.
    /// This function implements the Counter-Example Guided Abstraction Refinement loop.
    /// The function takes a set of definitions of the form "a->L" or "-a -> -L", where "a" is a Boolean variable in the skeleton of the formula and "L" is a first-order atom.
    /// The loop then iteratively solves an over-approximation by adding more and more definitions to the solver.
    /// If the over-abstraction is satisfiable, the model is checked against the original formula.
    /// If the model satisfies the formula, the formula is satisfiable.
    /// If the model does not satisfy the formula, then the model is used to refine the abstraction.
    /// The loop continues until the formula is proven to be unsatisfiable, or the solver gives up.
    fn solve_cegar(
        &mut self,
        fm: Node,
        mut solver: Solver,
        mut defs: Vec<LitDefinition>,
        mngr: &mut NodeManager,
    ) -> Result<SolverAnswer, Error> {
        let mut blocked = 0;
        loop {
            // Try to solve the current over-approximation. The first call only contains the skeleton.
            match solver.solve(mngr)? {
                SolverAnswer::Sat(h) => {
                    // SAT, check if the model is a solution for the original formula
                    let model = h.unwrap();
                    let h = model.clone().into();
                    log::debug!("Found model for over-approximation");
                    log::trace!("Model: {}", model);
                    if self.check_assignment(&fm, &h) {
                        // If the model satisfies the formula, we are done
                        return Ok(SolverAnswer::Sat(Some(model)));
                    } else {
                        // Over-approximation is SAT, but model does not satisfy the formula
                        // Pick the next definitions to encode
                        log::info!("Model does not satisfy the formula");
                        let next = self.pick_defs(&fm, &h, &defs);
                        if next.is_empty() {
                            // In the future, this should block the current assignment and continue to search for a new model
                            // But we freeze the bounds to the current ones and return if no model can be found after max_blocking attemps
                            if blocked == 0 {
                                log::info!(
                                    "No more definitions to add. Trying to find a new model."
                                );
                                solver.freeze_bounds();
                            }
                            solver.block(&h);
                            blocked += 1;
                            if blocked > self.options.max_blocking {
                                log::info!("Too many blocked assignments. Giving up.");
                                return Ok(SolverAnswer::Unknown);
                            }
                        } else {
                            // Add the next definitions to the solver
                            for d in next {
                                log::info!("Adding literal: {}", d);
                                solver.add_definition(&d);
                                defs.retain(|def| def.defining() != d.defining());
                            }
                        }
                    }
                }
                SolverAnswer::Unsat if blocked == 0 => return Ok(SolverAnswer::Unsat), // Over-approximation is UNSAT, the formula is UNSAT
                SolverAnswer::Unsat => {
                    // Over-approximation is UNSAT, but we have blocked assignments
                    // The over-approximation might be unsat because there are no more assignment
                    //  We must return unknown in this case
                    return Ok(SolverAnswer::Unknown);
                }
                SolverAnswer::Unknown => return Ok(SolverAnswer::Unknown),
            }
        }
    }

    /// Pick the next definition(s) to encode.
    /// Currently, this is a no-op, and just returns the input definitions.
    /// That is, all definitions are encoded after the first iteration.
    fn pick_defs<'a>(
        &self,
        _fm: &Node,
        _assign: &Assignment,
        defs: &'a [LitDefinition],
    ) -> Vec<LitDefinition> {
        let mut boolvars = Vec::new();
        // "x=y" and "x=w"
        let mut simple_eqs = Vec::new();
        // "x in R" with simple regex R, also factor relations
        let mut simple_inres = Vec::new();
        // "x in R" with complex regex R (intersection, complement, diff)
        let mut extended_inres: Vec<LitDefinition> = Vec::new();
        // Propagate word equations
        let mut weqs = Vec::new();
        // Lenght constraints
        let mut lc = Vec::new();
        for d in defs {
            let lit = d.defined();
            match lit.atom().kind() {
                AtomKind::Boolvar(_) => boolvars.push(d.clone()),
                AtomKind::WordEquation(weq) => match weq {
                    WordEquation::ConstantEquality(_, _) => unreachable!(),
                    WordEquation::VarEquality(_, _) => simple_eqs.push(d.clone()),
                    WordEquation::VarAssignment(_, _) => simple_eqs.push(d.clone()),
                    WordEquation::General(_, _) => weqs.push(d.clone()),
                },
                AtomKind::InRe(inre) => {
                    if inre.re().simple() {
                        simple_inres.push(d.clone());
                    } else {
                        extended_inres.push(d.clone());
                    }
                }
                AtomKind::FactorConstraint(_) => simple_inres.push(d.clone()),
                AtomKind::Linear(_) => lc.push(d.clone()),
            }
        }
        let mut result = boolvars;
        result.extend(simple_eqs);
        result.extend(simple_inres);
        if !result.is_empty() {
            return result;
        }
        // add word equations and length constraints
        result.extend(weqs);
        result.extend(lc);
        if !result.is_empty() {
            return result;
        }
        // add extended inres
        let posneg: (Vec<LitDefinition>, Vec<LitDefinition>) = extended_inres
            .into_iter()
            .partition(|d| d.defined().polarity());
        // first only the positiv
        result.extend(posneg.0);
        if !result.is_empty() {
            return result;
        }
        // then the negative
        result.extend(posneg.1);
        result
    }

    /// Initialize the domain of all variables in the formula.
    /// The domain is the range of values that a variable can take.
    /// The domain is encoded as the first step of the encoding.
    fn _init_domain_exact(&self, fm: &Node, mngr: &mut NodeManager) -> Option<Domain> {
        let mut inferer = BoundInferer::default();
        for lit in get_entailed_literals(fm) {
            inferer.add_literal(lit.clone(), mngr)
        }

        let init_bounds = inferer.infer()?;
        // Clamp all bounds and add Booleans to the domain
        let mut domain = Domain::default();
        for v in fm.variables() {
            match v.sort() {
                Sort::Int | Sort::String => {
                    let lower = init_bounds
                        .get(&v)
                        .and_then(|b| b.lower_finite())
                        .unwrap_or(0);
                    let upper = init_bounds
                        .get(&v)
                        .and_then(|b| b.upper_finite())
                        .unwrap_or(self.options.init_upper_bound)
                        .max(lower) // at least lower
                        .max(1); // at least 1
                    let interval = Interval::new(lower, upper);
                    // Clamp the bound to max
                    let interval = interval.intersect(self.options.max_bounds);
                    match v.sort() {
                        Sort::Int => domain.set_int(v.clone(), interval),
                        Sort::String => domain.set_string(v.clone(), interval),
                        _ => unreachable!(),
                    };
                }
                Sort::Bool => domain.set_bool(v.clone()),
                Sort::RegLan => unreachable!(),
            };
        }
        Some(domain)
    }

    /// Initialize the domain of all variables in the formula.
    /// The domain is the range of values that a variable can take.
    /// The domain is encoded as the first step of the encoding.
    fn init_domain_approx(&self, fm: &Node, _mngr: &mut NodeManager) -> Option<Domain> {
        let mut seen: IndexSet<Literal> = IndexSet::new();
        let mut refiner = LinearRefiner::default();
        for lit in get_entailed_literals(fm) {
            seen.insert(lit.clone());
            if seen.contains(&lit.flip_polarity()) {
                return None;
            }
            match lit.atom().kind() {
                AtomKind::InRe(inre) if lit.polarity() => {
                    let re = inre.re();
                    if let Some(s) = re_smallest(re) {
                        // |x| >= s

                        let lc = LinearConstraint::new(
                            LinearArithTerm::from_var(inre.lhs().clone()),
                            ArithOperator::Geq,
                            s as i64,
                        );
                        refiner.add_linear(lc);
                    }
                    if let Some(s) = re_longest(re) {
                        // |x| <= s
                        let lc = LinearConstraint::new(
                            LinearArithTerm::from_var(inre.lhs().clone()),
                            ArithOperator::Leq,
                            s as i64,
                        );
                        refiner.add_linear(lc);
                    }
                }
                AtomKind::WordEquation(weq) if lit.polarity() => refiner.add_weq(weq),
                _ => (),
            }
        }

        let init_bounds = refiner.infer()?;
        // Clamp all bounds and add Booleans to the domain
        let mut domain = Domain::default();
        for v in fm.variables() {
            match v.sort() {
                Sort::Int | Sort::String => {
                    let lower = init_bounds
                        .get(&v)
                        .and_then(|b| b.lower_finite())
                        .unwrap_or(0);
                    let upper = init_bounds
                        .get(&v)
                        .and_then(|b| b.upper_finite())
                        .unwrap_or(self.options.init_upper_bound)
                        .max(lower) // at least lower
                        .max(1); // at least 1
                    let interval = Interval::new(lower, upper);
                    // Clamp the bound to max
                    let interval = interval.intersect(self.options.max_bounds);
                    match v.sort() {
                        Sort::Int => domain.set_int(v.clone(), interval),
                        Sort::String => domain.set_string(v.clone(), interval),
                        _ => unreachable!(),
                    };
                }
                Sort::Bool => domain.set_bool(v.clone()),
                Sort::RegLan => unreachable!(),
            };
        }
        Some(domain)
    }

    /// Check if the assignment is a solution for the formula.
    /// Returns true if the assignment satisfies the formula.
    /// Returns false if the assignment does not satisfy the formula.
    /// Also returns false if the assignment is is incomplete, i.e., if it does not assign a value to all variables.
    fn check_assignment(&self, fm: &Node, assign: &Assignment) -> bool {
        assign.satisfies(fm).unwrap_or(false)
    }
}

fn re_smallest(re: &Regex) -> Option<usize> {
    match re.op() {
        ReOp::Literal(word) => Some(word.len()),
        ReOp::Range(r) if !r.is_empty() => Some(1),
        ReOp::None => None,
        ReOp::Any => Some(1),
        ReOp::All => Some(0),
        ReOp::Concat(rs) => {
            let mut sum = 0;
            for r in rs {
                sum += re_smallest(r)?;
            }
            Some(sum)
        }
        ReOp::Union(rs) | ReOp::Inter(rs) => {
            let mut min = usize::MAX;
            for r in rs {
                if let Some(s) = re_smallest(r) {
                    min = min.min(s);
                }
            }
            if min == usize::MAX {
                None
            } else {
                Some(min)
            }
        }
        ReOp::Star(_) | ReOp::Opt(_) | ReOp::Pow(_, 0) | ReOp::Loop(_, 0, _) => Some(0),
        ReOp::Plus(r) => re_smallest(r),
        ReOp::Pow(r, p) => re_smallest(r).map(|s| s * (*p as usize)),
        ReOp::Loop(r, l, u) if l <= u => re_smallest(r).map(|s| s * (*l as usize)),
        _ => None,
    }
}

fn re_longest(re: &Regex) -> Option<usize> {
    match re.op() {
        ReOp::Literal(word) => Some(word.len()),
        ReOp::Range(r) if !r.is_empty() => Some(1),
        ReOp::None => None,
        ReOp::Any => Some(1),
        ReOp::All => None,
        ReOp::Concat(rs) => {
            let mut sum = 0;
            for r in rs {
                sum += re_longest(r)?;
            }
            Some(sum)
        }
        ReOp::Union(rs) | ReOp::Inter(rs) => {
            let mut max: isize = -1;
            for r in rs {
                if let Some(s) = re_longest(r) {
                    max = max.min(s as isize);
                }
            }
            if max == -1 {
                None
            } else {
                Some(max as usize)
            }
        }
        ReOp::Star(_) => None,
        ReOp::Opt(r) | ReOp::Plus(r) => re_longest(r),
        ReOp::Pow(_, 0) | ReOp::Loop(_, _, 0) => Some(0),
        ReOp::Pow(r, p) => re_longest(r).map(|s| s * (*p as usize)),
        ReOp::Loop(r, l, u) if l <= u => re_longest(r).map(|s| s * (*u as usize)),
        _ => None,
    }
}
