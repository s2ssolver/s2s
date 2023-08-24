//! Implementation of the automaton-based encoding of regular constraints.
//! The encoding was first introduced in the paper
//!
//! > Kulczynski, M., Lotz, K., Nowotka, D., Poulsen, D.B. (2022). *Solving String Theories Involving Regular Membership Predicates Using SAT*. In: Legunsen, O., Rosu, G. (eds) Model Checking Software. SPIN 2022. Lecture Notes in Computer Science, vol 13255. Springer, Cham. https://doi.org/10.1007/978-3-031-15077-7_8
//!
//! This module contains the enhanced version of the encoding, which allows for incremental solving. This version is described in the paper
//!
//! > TODO: Add CAV paper reference

use std::cmp::{max, min};

use indexmap::IndexMap;
use regulaer::{
    automaton::{Automaton, AutomatonError, State, TransitionType},
    re::Regex,
};

use crate::{
    bounds::Bounds,
    encode::{domain::DomainEncoding, ConstraintEncoder, EncodingResult, LAMBDA},
    error::Error,
    model::{
        constraints::{RegularConstraint, RegularConstraintType, Symbol},
        Variable,
    },
    sat::{as_lit, neg, pvar, PVar},
};

const NFA_NOT_EPSILON_FREE_MSG: &str = "NFA must be epsilon-free";

/// An encoder for regular constraints using automata.
/// Encodes that a variable is a member of a regular language.
/// The resulting encoding is incremental.
pub struct NFAEncoder {
    var: Variable,
    nfa: Automaton<char>,
    regex: Regex<char>,

    /// The bounds of the variable in the previous round.
    /// If `None`, the variable was not yet encoded, i.e., prior to the first encoding.
    last_bound: Option<usize>,

    /// Maps a state and a bound to a propositional variable that is true iff the automaton is in the given state after reading the given number of characters.
    reach_vars: IndexMap<(State, usize), PVar>,

    /// A selector variable that is added to the assumptions for the current bound
    bound_selector: Option<PVar>,

    /// Whether the constraint is positive or negative
    sign: bool,
}

impl NFAEncoder {
    /// Incrementally adds the reachability vars for the increased bound.
    fn create_reach_vars(&mut self, bound: usize) {
        let last_bound = self.last_bound.unwrap_or(0);
        for l in last_bound..=bound {
            for state in self.nfa.states() {
                self.reach_vars.insert((state, l), pvar());
            }
        }
    }

    fn encode_intial(&self) -> EncodingResult {
        if self.last_bound.is_none() {
            let mut res = EncodingResult::empty();
            // Only encode in first round
            for state in self.nfa.states() {
                if Some(state) == self.nfa.initial() {
                    // Initial state is reachable after reading 0 characters
                    res.add_clause(vec![as_lit(self.reach_vars[&(state, 0)])]);
                } else {
                    // All other states are not reachable after reading 0 characters

                    res.add_clause(vec![neg(self.reach_vars[&(state, 0)])]);
                }
            }
            res
        } else {
            EncodingResult::Trivial(true)
        }
    }

    /// Encodes the set of transitions of the automaton.
    fn encode_transitions(
        &self,
        bound: usize,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(0);

        for l in last_bound..bound {
            for state in self.nfa.states() {
                let reach_var = self.reach_vars[&(state, l)];

                for transition in self.nfa.transitions_for(&state)? {
                    let reach_next = self.reach_vars[&(transition.get_dest(), l + 1)];
                    match transition.get_type() {
                        TransitionType::Symbol(c) => {
                            // Follow transition if we read the given character
                            let sub_var = dom.string().get(&self.var, l, *c).unwrap();
                            let clause = vec![neg(reach_var), neg(sub_var), as_lit(reach_next)];
                            res.add_clause(clause);
                        }
                        TransitionType::Range(lb, ub) => {
                            // Follow transition if we read a character in the given range
                            for c in *lb..=*ub {
                                let sub_var = dom.string().get(&self.var, l, c).unwrap();
                                let clause = vec![neg(reach_var), neg(sub_var), as_lit(reach_next)];
                                res.add_clause(clause);
                            }
                        }
                        TransitionType::Any => {
                            // Follow transition if we do not read lambda
                            let lambda_sub_var = dom.string().get(&self.var, l, LAMBDA).unwrap();
                            let clause =
                                vec![neg(reach_var), as_lit(lambda_sub_var), as_lit(reach_next)];
                            res.add_clause(clause);
                        }
                        TransitionType::Epsilon => {
                            // That must not happen
                            return Err(Error::EncodingError(NFA_NOT_EPSILON_FREE_MSG.to_string()));
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_next = self.reach_vars[&(state, l + 1)];
                let lambda_sub_var = dom.string().get(&self.var, l, LAMBDA).unwrap();
                let clause = vec![neg(reach_var), neg(lambda_sub_var), as_lit(reach_next)];
                res.add_clause(clause);
            }
        }
        Ok(res)
    }

    fn encode_predecessor(
        &self,
        bound: usize,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(0);

        for l in (last_bound + 1)..=bound {
            for state in self.nfa.states() {
                let reach_var = self.reach_vars[&(state, l)];
                let mut alo_clause = vec![neg(reach_var)];

                for pred in self.nfa.predecessors_for(&state)? {
                    let reach_prev = self.reach_vars[&(pred.get_dest(), l - 1)];
                    // Tseitin on-the-fly
                    let def_var = pvar();
                    alo_clause.push(as_lit(def_var));
                    match pred.get_type() {
                        TransitionType::Symbol(c) => {
                            // Is predecessor if we read the given character
                            let sub_var = dom.string().get(&self.var, l - 1, *c).unwrap();
                            res.add_clause(vec![neg(def_var), as_lit(reach_prev)]);
                            res.add_clause(vec![neg(def_var), as_lit(sub_var)]);
                        }
                        TransitionType::Range(lb, ub) => {
                            // Is predecessor if we read a character in the given range
                            res.add_clause(vec![neg(def_var), as_lit(reach_prev)]);
                            let mut range_clause = vec![neg(def_var)];
                            for c in *lb..=*ub {
                                let sub_var = dom.string().get(&self.var, l - 1, c).unwrap();
                                range_clause.push(as_lit(sub_var));
                            }
                            res.add_clause(range_clause);
                        }
                        TransitionType::Any => {
                            // Is predecessor if we do not read lambda
                            let sub_var = dom.string().get(&self.var, l - 1, LAMBDA).unwrap();
                            res.add_clause(vec![neg(def_var), as_lit(reach_prev)]);
                            res.add_clause(vec![neg(def_var), neg(sub_var)]);
                        }
                        TransitionType::Epsilon => {
                            return Err(Error::EncodingError(NFA_NOT_EPSILON_FREE_MSG.to_string()))
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_prev = self.reach_vars[&(state, l - 1)];
                let lambda_sub_var = dom.string().get(&self.var, l - 1, LAMBDA).unwrap();
                let def_var = pvar();
                alo_clause.push(as_lit(def_var));
                res.add_clause(vec![neg(def_var), as_lit(reach_prev)]);
                res.add_clause(vec![neg(def_var), as_lit(lambda_sub_var)]);

                res.add_clause(alo_clause);
            }
        }

        Ok(res)
    }

    fn encode_final(&self, bound: usize) -> EncodingResult {
        if self.sign {
            self.encode_final_positive(bound)
        } else {
            self.encode_final_negative(bound)
        }
    }

    fn encode_final_positive(&self, bound: usize) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let selector = self.bound_selector.unwrap();

        let mut clause = vec![neg(selector)];
        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(*qf, bound)];
            clause.push(as_lit(reach_var));
        }
        res.add_clause(clause);
        res
    }

    fn encode_final_negative(&self, bound: usize) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let selector = self.bound_selector.unwrap();

        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(*qf, bound)];
            res.add_clause(vec![neg(selector), neg(reach_var)]);
        }

        res
    }
}

impl ConstraintEncoder for NFAEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        self.last_bound = None;
        self.reach_vars.clear();
        self.bound_selector = None;
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        substitution: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        if self.sign {
            log::debug!("Encoding `{} in {}` ", self.var, self.regex,);
        } else {
            log::debug!("Encoding `{} notin {}` ", self.var, self.regex,);
        }

        let bound = bounds
            .get_with_default(&self.var.len_var().unwrap())
            .get_upper()
            .unwrap_or(0) as usize;

        log::trace!("Bound: {}", bound);
        if Some(bound) == self.last_bound {
            log::trace!("Upper bound did not change, skipping encoding");
            if let Some(s) = self.bound_selector {
                return Ok(EncodingResult::assumption(as_lit(s)));
            } else {
                return Ok(EncodingResult::Trivial(true));
            }
        }
        let mut res = EncodingResult::empty();

        // Create new selector for this bound
        let selector = pvar();
        self.bound_selector = Some(selector);
        res.add_assumption(as_lit(selector));
        // Create reachability vars for this bound
        self.create_reach_vars(bound);

        let effective_bound = if self.nfa.acyclic() {
            let effective_bound = min(bound, max(self.nfa.states().len(), 1));
            if self.sign {
                // If the automaton is acyclic and constraint is positive, then lhs cannot be longer than the number of states
                // We use the number of states as the effective bound
                for l in effective_bound + 1..bound {
                    // Var cannot have this length
                    let len_var = self.var.len_var().unwrap();
                    let len_var = substitution.int().get(&len_var, l as isize).unwrap();
                    res.add_clause(vec![neg(len_var)]);
                }

                if self.last_bound.unwrap_or(0) >= effective_bound {
                    // If the last bound was greater than the effective bound, the automaton is already fully encoded

                    return Ok(res);
                }
                effective_bound
            } else {
                // If the automaton is acyclic and constraint is negative, then any lhs longer than the number of states trivially satisfies the constraint
                // We use the number of states +1  as the effective bound
                min(bound, effective_bound + 1)
            }
        } else {
            bound
        };

        let e_init = self.encode_intial();
        log::trace!("Encoded initial state: {} clauses", e_init.clauses());
        res.join(e_init);

        let e_transition = self.encode_transitions(effective_bound, substitution)?;
        log::trace!("Encoded transitions: {} clauses", e_transition.clauses());
        res.join(e_transition);

        let e_predecessor = self.encode_predecessor(effective_bound, substitution)?;
        log::trace!("Encoded predecessors: {} clauses", e_predecessor.clauses());
        res.join(e_predecessor);

        let e_final = self.encode_final(effective_bound);
        log::trace!("Encoded final state: {} clauses", e_final.clauses());
        res.join(e_final);

        self.last_bound = Some(bound);
        Ok(res)
    }
}

impl NFAEncoder {
    fn new(
        var: &Variable,
        automaton: &Automaton<char>,
        regex: &Regex<char>,
        ttype: RegularConstraintType,
    ) -> Self {
        // We clone the nfa because any changes would break the incremental encoding
        let mut nfa = automaton.clone();
        // Normalize the NFA
        nfa.normalize().unwrap();

        Self {
            var: var.clone(),
            nfa,
            sign: ttype.is_in(),
            regex: regex.clone(),
            last_bound: None,
            reach_vars: IndexMap::new(),
            bound_selector: None,
        }
    }
}

impl From<AutomatonError> for Error {
    fn from(err: AutomatonError) -> Self {
        Error::EncodingError(format!("Error while encoding NFA: {:?}", err))
    }
}

pub fn build_re_encoder(rec: RegularConstraint) -> Result<Box<dyn ConstraintEncoder>, Error> {
    let encoder: Box<dyn ConstraintEncoder> = if rec.get_pattern().len() == 1 {
        if let Some(Symbol::Variable(v)) = rec.get_pattern().symbols().next() {
            Box::new(NFAEncoder::new(
                v,
                rec.get_automaton().unwrap(),
                rec.get_re(),
                rec.get_type(),
            ))
        } else {
            return Err(Error::EncodingError(
                "Cannot encode constant pattern".to_string(),
            ));
        }
    } else {
        panic!("Cannot encode non-singleton patterns")
    };
    Ok(encoder)
}

#[cfg(test)]
mod test {
    use cadical::Solver;
    use indexmap::IndexSet;

    use regulaer::{automaton::compile, re::Regex, RegLang};

    use super::*;

    use crate::{
        bounds::IntDomain,
        encode::domain::{get_str_substitutions, DomainEncoder},
        instance::Instance,
        model::{
            constraints::{Pattern, RegularConstraintType},
            Sort, Variable,
        },
    };

    fn from_constraint(con: &RegularConstraint) -> Result<NFAEncoder, Error> {
        if con.get_pattern().len() == 1 {
            if let Some(Symbol::Variable(v)) = con.get_pattern().symbols().next() {
                return Ok(NFAEncoder::new(
                    v,
                    con.get_automaton().unwrap(),
                    con.get_re(),
                    con.get_type(),
                ));
            }
        }
        Err(Error::EncodingError(
            "Can only encode single variable patterns".to_string(),
        ))
    }

    fn solve_with_bounds(var: &Variable, re: Regex<char>, bounds: &[Bounds]) -> Option<bool> {
        let mut instance = Instance::default();
        instance.add_var(var.clone());

        let mut alph = IndexSet::from_iter(re.alphabet().into_iter());
        alph.insert('a');

        let mut constraint = RegularConstraint::new(
            re.clone(),
            Pattern::variable(var),
            RegularConstraintType::In,
        );
        constraint.compile(None).unwrap();
        let mut encoder = from_constraint(&constraint).unwrap();
        let mut dom_encoder = DomainEncoder::new(alph);
        let mut solver: Solver = cadical::Solver::default();

        let mut result = None;
        for bound in bounds {
            let mut res = EncodingResult::empty();
            res.join(dom_encoder.encode(bound, &instance));

            res.join(encoder.encode(bound, dom_encoder.encoding()).unwrap());

            match res {
                EncodingResult::Cnf(clauses, assms) => {
                    for clause in clauses.into_iter() {
                        solver.add_clause(clause);
                    }
                    result = solver.solve_with(assms.into_iter());
                    if let Some(true) = result {
                        let _model =
                            get_str_substitutions(dom_encoder.encoding(), &instance, &solver);
                        let var_model = _model.get(var).unwrap();
                        assert!(
                            re.contains(var_model),
                            "Model {:?} does not match regex {:?}",
                            var_model,
                            re
                        );

                        return Some(true);
                    }
                }
                _ => unreachable!(),
            }
        }
        result
    }

    #[test]
    fn var_in_epsi() {
        let var = Variable::temp(Sort::String);
        let re = Regex::epsilon();
        let mut bounds = Bounds::with_defaults(IntDomain::Bounded(0, 0));
        bounds.set(&var.len_var().unwrap(), IntDomain::Bounded(0, 1));

        assert_eq!(solve_with_bounds(&var, re, &[bounds]), Some(true));
    }

    #[test]
    fn var_in_none() {
        let var = Variable::temp(Sort::String);
        let re = Regex::none();
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));

        assert_eq!(solve_with_bounds(&var, re, &[bounds]), Some(false));
    }

    #[test]
    fn var_in_const() {
        let var = Variable::temp(Sort::String);
        let re = Regex::word("foo");
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        let mut nfa = compile(&re).unwrap();
        nfa.normalize().unwrap();

        assert_eq!(solve_with_bounds(&var, re, &[bounds]), Some(true));
    }

    #[test]
    fn var_in_const_concat() {
        let var = Variable::temp(Sort::String);
        let re = Regex::concat(vec![Regex::word("foo"), Regex::word("bar")]);
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        let mut nfa = compile(&re).unwrap();
        nfa.normalize().unwrap();

        assert_eq!(solve_with_bounds(&var, re, &[bounds]), Some(true));
    }
}
