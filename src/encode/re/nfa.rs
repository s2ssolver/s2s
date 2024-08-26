//! Implementation of the automaton-based encoding of regular constraints.
//! The encoding was first introduced in the paper
//!
//! > Kulczynski, M., Lotz, K., Nowotka, D., Poulsen, D.B. (2022). *Solving String Theories Involving Regular Membership Predicates Using SAT*. In: Legunsen, O., Rosu, G. (eds) Model Checking Software. SPIN 2022. Lecture Notes in Computer Science, vol 13255. Springer, Cham. https://doi.org/10.1007/978-3-031-15077-7_8
//!
//! This module contains the enhanced version of the encoding, which allows for incremental solving. This version is described in the paper
//!
//! > TODO: Add CAV paper reference

use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};
use regulaer::{
    alph::CharRange,
    automaton::{AutomatonError, State, StateId, Transition, TransitionType, NFA},
    re::Regex,
};

use crate::{
    bounds::Bounds,
    context::Context,
    encode::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder, LAMBDA},
    repr::{
        ir::{RegularConstraint, Symbol},
        Variable,
    },
    sat::{nlit, plit, pvar, PVar},
};

const NFA_NOT_EPSILON_FREE_MSG: &str = "NFA must be epsilon-free";

/// An encoder for regular constraints using automata.
/// Encodes that a variable is a member of a regular language.
/// The resulting encoding is incremental.
pub struct NFAEncoder {
    var: Variable,
    nfa: Rc<NFA>,
    /// The inverse of the transition function.
    /// Maps a state to a list of pairs (state, transition) that lead to the given state.
    delta_inv: IndexMap<StateId, Vec<(StateId, Transition)>>,

    regex: Regex,

    /// The bounds of the variable in the previous round.
    /// If `None`, the variable was not yet encoded, i.e., prior to the first encoding.
    last_bound: Option<usize>,

    /// Maps a state and a bound to a propositional variable that is true iff the automaton is in the given state after reading the given number of characters.
    reach_vars: IndexMap<(StateId, usize), PVar>,

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
                    res.add_clause(vec![plit(self.reach_vars[&(state, 0)])]);
                } else {
                    // All other states are not reachable after reading 0 characters

                    res.add_clause(vec![nlit(self.reach_vars[&(state, 0)])]);
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
    ) -> Result<EncodingResult, EncodingError> {
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(0);

        for l in last_bound.saturating_sub(1)..bound {
            for state in self.nfa.states() {
                let reach_var = self.reach_vars[&(state, l)];

                for transition in self.nfa.get_state(state)?.transitions() {
                    let reach_next = self.reach_vars[&(transition.get_dest(), l + 1)];
                    match transition.get_type() {
                        TransitionType::Range(range) if range_any(&range) => {
                            // Follow transition if we do not read lambda
                            let lambda_sub_var =
                                dom.string().get_sub(&self.var, l, LAMBDA).unwrap();
                            let clause =
                                vec![nlit(reach_var), plit(lambda_sub_var), plit(reach_next)];
                            res.add_clause(clause);
                        }
                        TransitionType::Range(range) => {
                            let lb = range.start();
                            let ub = range.end();

                            // Follow transition if we read a character in the given range
                            for c in lb..=ub {
                                let sub_var = dom.string().get_sub(&self.var, l, c).expect(
                                    format!(
                                        "Substitution h({})[{}] = {} not found",
                                        self.var, l, c
                                    )
                                    .as_str(),
                                );
                                let clause = vec![nlit(reach_var), nlit(sub_var), plit(reach_next)];
                                res.add_clause(clause);
                            }
                        }
                        TransitionType::Epsilon => {
                            // That must not happen
                            return Err(EncodingError::new(NFA_NOT_EPSILON_FREE_MSG));
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_next = self.reach_vars[&(state, l + 1)];
                let lambda_sub_var = dom.string().get_sub(&self.var, l, LAMBDA).unwrap();
                let clause = vec![nlit(reach_var), nlit(lambda_sub_var), plit(reach_next)];
                res.add_clause(clause);
            }
        }
        Ok(res)
    }

    fn encode_predecessor(
        &self,
        bound: usize,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(1);

        for l in last_bound..=bound {
            for (state, preds) in self.delta_inv.iter() {
                let reach_var = self.reach_vars[&(*state, l)];
                let mut alo_clause = vec![nlit(reach_var)];

                for (q_pred, trans) in preds.iter() {
                    debug_assert!(trans.get_dest() == *state);
                    let reach_prev = self.reach_vars[&(*q_pred, l - 1)];
                    // Tseitin on-the-fly
                    let def_var = pvar();
                    alo_clause.push(plit(def_var));
                    match trans.get_type() {
                        TransitionType::Range(range) if range_any(range) => {
                            // Is predecessor if we do not read lambda
                            let sub_var = dom.string().get_sub(&self.var, l - 1, LAMBDA).unwrap();
                            res.add_clause(vec![nlit(def_var), plit(reach_prev)]);
                            res.add_clause(vec![nlit(def_var), nlit(sub_var)]);
                        }
                        TransitionType::Range(range) => {
                            // Is predecessor if we read a character in the given range
                            let lb = range.start();
                            let ub = range.end();
                            res.add_clause(vec![nlit(def_var), plit(reach_prev)]);
                            let mut range_clause = vec![nlit(def_var)];
                            for c in lb..=ub {
                                let sub_var = dom.string().get_sub(&self.var, l - 1, c).unwrap();
                                range_clause.push(plit(sub_var));
                            }
                            res.add_clause(range_clause);
                        }
                        TransitionType::Epsilon => {
                            return Err(EncodingError::new(NFA_NOT_EPSILON_FREE_MSG))
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_prev = self.reach_vars[&(*state, l - 1)];
                let lambda_sub_var = dom.string().get_sub(&self.var, l - 1, LAMBDA).unwrap();
                let def_var = pvar();
                alo_clause.push(plit(def_var));
                res.add_clause(vec![nlit(def_var), plit(reach_prev)]);
                res.add_clause(vec![nlit(def_var), plit(lambda_sub_var)]);

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

        let mut clause = vec![nlit(selector)];
        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(*qf, bound)];
            clause.push(plit(reach_var));
        }
        res.add_clause(clause);
        res
    }

    fn encode_final_negative(&self, bound: usize) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let selector = self.bound_selector.unwrap();

        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(*qf, bound)];
            res.add_clause(vec![nlit(selector), nlit(reach_var)]);
        }

        res
    }
}

impl LiteralEncoder for NFAEncoder {
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
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.sign {
            log::debug!("Encoding `{} in {}` ", self.var, self.regex,);
        } else {
            log::debug!("Encoding `{} notin {}` ", self.var, self.regex,);
        }

        let bound = bounds.get_upper_finite(&self.var).unwrap_or(0) as usize;

        log::trace!("Bound: {}", bound);
        if Some(bound) == self.last_bound {
            log::trace!("Upper bound did not change, skipping encoding");
            if let Some(s) = self.bound_selector {
                return Ok(EncodingResult::assumption(plit(s)));
            } else {
                return Ok(EncodingResult::Trivial(true));
            }
        }
        let mut res = EncodingResult::empty();

        // Create new selector for this bound
        let selector = pvar();
        self.bound_selector = Some(selector);
        res.add_assumption(plit(selector));
        // Create reachability vars for this bound
        self.create_reach_vars(bound);

        let effective_bound = bound; /*if self.nfa.acyclic() {
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
                                     };*/

        let e_init = self.encode_intial();
        log::trace!("Encoded initial state: {} clauses", e_init.clauses());
        res.extend(e_init);

        let e_transition = self.encode_transitions(effective_bound, dom)?;
        log::trace!("Encoded transitions: {} clauses", e_transition.clauses());
        res.extend(e_transition);

        let e_predecessor = self.encode_predecessor(effective_bound, dom)?;
        log::trace!("Encoded predecessors: {} clauses", e_predecessor.clauses());
        res.extend(e_predecessor);

        let e_final = self.encode_final(effective_bound);
        log::trace!("Encoded final state: {} clauses", e_final.clauses());
        res.extend(e_final);

        self.last_bound = Some(bound);
        Ok(res)
    }
}

impl NFAEncoder {
    fn new(var: &Variable, nfa: Rc<NFA>, regex: &Regex, pol: bool) -> Self {
        let delta_inv = precompute_delta_inv(&nfa).unwrap();
        Self {
            var: var.clone(),
            nfa,
            delta_inv,
            sign: pol,
            regex: regex.clone(),
            last_bound: None,
            reach_vars: IndexMap::new(),
            bound_selector: None,
        }
    }
}

impl From<AutomatonError> for EncodingError {
    fn from(err: AutomatonError) -> Self {
        EncodingError::new(&err.to_string())
    }
}

pub fn build_inre_encoder(
    inre: &RegularConstraint,
    pol: bool,
    ctx: &mut Context,
) -> Result<Box<dyn LiteralEncoder>, EncodingError> {
    let p = inre.pattern();
    let re = inre.re();
    let encoder: Box<dyn LiteralEncoder> = if p.is_variable() {
        if let Some(Symbol::Variable(v)) = p.first() {
            let nfa = ctx.get_nfa(re);
            Box::new(NFAEncoder::new(v, nfa, re, pol))
        } else {
            unreachable!()
        }
    } else {
        panic!("Cannot encode non-singleton patterns")
    };
    Ok(encoder)
}

/* Some auxiliary functions */

const SMT_MAX_CHAR: u32 = 196607;
fn range_any(r: &CharRange) -> bool {
    r.start() as u32 == 0 && r.end() as u32 == SMT_MAX_CHAR
}

fn precompute_delta_inv(
    nfa: &Rc<NFA>,
) -> Result<IndexMap<StateId, Vec<(StateId, Transition)>>, AutomatonError> {
    let mut delta_inv = IndexMap::new();

    // Do one DFS
    if let Some(initial) = nfa.initial() {
        let mut stack = vec![initial];
        let mut visited = IndexSet::new();
        visited.insert(initial);

        while let Some(state) = stack.pop() {
            for transition in nfa.get_state(state)?.transitions() {
                let dest = transition.get_dest();
                let entry = delta_inv.entry(dest).or_insert_with(Vec::new);
                entry.push((state, transition));
                if !visited.contains(&dest) {
                    stack.push(dest);
                }
            }
        }
    }
    Ok(delta_inv)
}

#[cfg(test)]
mod test {
    use cadical::Solver;
    use regulaer::re::ReBuilder;

    use super::*;

    use crate::{
        alphabet::Alphabet,
        bounds::Interval,
        encode::domain::{encoding::get_str_substitutions, DomainEncoder},
        repr::Sort,
    };

    fn solve_with_bounds(re: Regex, pol: bool, ubounds: &[usize]) -> Option<bool> {
        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);

        let mut alph = Alphabet::from(re.operator().alphabet());
        alph.insert_char('a');

        let nfa = ctx.get_nfa(&re);

        let mut bounds = Bounds::default();

        let mut encoder = NFAEncoder::new(&var, nfa, &re, pol);
        let mut dom_encoder = DomainEncoder::new(alph);
        let mut solver: Solver = cadical::Solver::default();

        let mut result = None;
        for bound in ubounds {
            bounds.set(var.as_ref().clone(), Interval::new(0, *bound as isize));
            let mut res = EncodingResult::empty();

            res.extend(dom_encoder.encode(&bounds, &ctx));

            res.extend(encoder.encode(&bounds, dom_encoder.encoding()).unwrap());

            match res {
                EncodingResult::Cnf(clauses, assms) => {
                    for clause in clauses.into_iter() {
                        solver.add_clause(clause);
                    }
                    result = solver.solve_with(assms.into_iter());
                    if let Some(true) = result {
                        let _model = get_str_substitutions(dom_encoder.encoding(), &ctx, &solver);
                        let var_model = _model.get(&var).unwrap().iter().collect::<String>();
                        assert!(
                            re.accepts(&var_model.clone().into()),
                            "Model `{}` does not match regex `{}`",
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
        let mut ctx = Context::default();

        let re = ctx.ast_builder().re_builder().epsilon();

        assert_eq!(solve_with_bounds(re, true, &[1]), Some(true));
    }

    #[test]
    fn var_in_none() {
        let mut ctx = Context::default();

        let re = ctx.ast_builder().re_builder().none();

        assert_eq!(solve_with_bounds(re, true, &[10]), Some(false));
    }

    #[test]
    fn var_in_const() {
        let mut ctx = Context::default();

        let re = ctx.ast_builder().re_builder().word("foo".into());

        assert_eq!(solve_with_bounds(re, true, &[10]), Some(true));
    }

    #[test]
    fn var_in_const_concat() {
        let mut ctx = Context::default();

        let builder = ctx.ast_builder().re_builder();

        let args = vec![builder.word("foo".into()), builder.word("bar".into())];
        let re = builder.concat(args);

        assert_eq!(solve_with_bounds(re, true, &[10]), Some(true));
    }
}
