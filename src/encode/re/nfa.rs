//! Implementation of the automaton-based encoding of regular constraints.
//! The encoding was first introduced in the paper
//!
//! > Kulczynski, M., Lotz, K., Nowotka, D., Poulsen, D.B. (2022). *Solving String Theories Involving Regular Membership Predicates Using SAT*. In: Legunsen, O., Rosu, G. (eds) Model Checking Software. SPIN 2022. Lecture Notes in Computer Science, vol 13255. Springer, Cham. https://doi.org/10.1007/978-3-031-15077-7_8
//!
//! This module contains the enhanced version of the encoding, which allows for incremental solving. This version is described in the paper

use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};
use rustsat::{clause, instances::Cnf, types::Clause};
use smt_str::automata::{StateId, StateNotFound, TransitionType, NFA};

use crate::{
    context::Variable,
    domain::Domain,
    encode::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink, LAMBDA},
    sat::{nlit, plit, pvar, PVar},
};

/// An encoder for regular constraints using automata.
/// Encodes that a variable is a member of a regular language.
/// The resulting encoding is incremental.
pub struct NFAEncoder {
    var: Rc<Variable>,
    nfa: Rc<NFA>,
    /// The inverse of the transition function.
    /// Maps a state to a list of pairs (state, transition) that lead to the given state.
    delta_inv: IndexMap<StateId, Vec<(StateId, TransitionType)>>,

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
        let last_bound = self.last_bound.map(|l| l + 1).unwrap_or(0);
        for l in last_bound..=bound {
            for state in self.nfa.states() {
                let ok = self.reach_vars.insert((state, l), pvar());
                assert!(ok.is_none());
            }
        }
    }

    fn encode_intial(&self, sink: &mut impl EncodingSink) {
        if self.last_bound.is_none() {
            let mut res = Cnf::new();
            // Only encode in first round
            for state in self.nfa.states() {
                if Some(state) == self.nfa.initial() {
                    // Initial state is reachable after reading 0 characters
                    res.add_unit(plit(self.reach_vars[&(state, 0)]));
                } else {
                    // All other states are not reachable after reading 0 characters
                    res.add_unit(nlit(self.reach_vars[&(state, 0)]));
                }
            }
            sink.add_cnf(res);
        }
    }

    /// Encodes the set of transitions of the automaton.
    fn encode_transitions(
        &self,
        bound: usize,
        dom: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let last_bound = self.last_bound.unwrap_or(0);
        for l in last_bound.saturating_sub(1)..bound {
            for state in self.nfa.states() {
                let reach_var = self.reach_vars[&(state, l)];

                for transition in self.nfa.transitions_from(state)? {
                    let reach_next = self.reach_vars[&(transition.get_dest(), l + 1)];
                    match transition.get_type() {
                        TransitionType::Range(range) if range.is_full() => {
                            // Follow transition if we do not read lambda
                            let lambda_sub_var =
                                dom.string().get_sub(&self.var, l, LAMBDA).unwrap();

                            // reach_var /\ -lambda_sub_var => reach_next
                            let clause = Clause::from([
                                nlit(reach_var),
                                plit(lambda_sub_var),
                                plit(reach_next),
                            ]);
                            sink.add_clause(clause);
                        }
                        TransitionType::Range(range) => {
                            // Follow transition if we read a character in the given range
                            for c in range.iter() {
                                let sub_var = match dom.string().get_sub(&self.var, l, c) {
                                    Some(v) => v,
                                    None => {
                                        panic!(
                                            "Substitution h({})[{}] = '{}' not found\n{}",
                                            self.var,
                                            l,
                                            c,
                                            self.nfa.dot()
                                        )
                                    }
                                };
                                // reach_var /\ sub_var => reach_next
                                let clause = Clause::from([
                                    nlit(reach_var),
                                    nlit(sub_var),
                                    plit(reach_next),
                                ]);
                                sink.add_clause(clause);
                            }
                        }
                        TransitionType::NotRange(range) => {
                            // Follow transition if we read a character **NOT** in the given range
                            for c in range.iter() {
                                let sub_var =
                                    dom.string().get_sub(&self.var, l, c).unwrap_or_else(|| {
                                        panic!(
                                            "Substitution h({})[{}] = '{}' not found",
                                            self.var, l, c
                                        )
                                    });
                                // reach_var /\ sub_var => reach_next
                                let clause = Clause::from([
                                    nlit(reach_var),
                                    plit(sub_var),
                                    plit(reach_next),
                                ]);
                                sink.add_clause(clause);
                            }
                        }
                        TransitionType::Epsilon => {
                            // That must not happen
                            return Err(EncodingError::not_epsi_free());
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_self = self.reach_vars[&(state, l + 1)];
                let lambda_sub_var = dom.string().get_sub(&self.var, l, LAMBDA).unwrap();
                // reach_var /\ lambda_sub_var => reach_next
                let clause =
                    Clause::from([nlit(reach_var), nlit(lambda_sub_var), plit(reach_self)]);
                sink.add_clause(clause);
            }
        }
        Ok(())
    }

    fn encode_predecessor(
        &self,
        bound: usize,
        dom: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let last_bound = self.last_bound.unwrap_or(1);

        for l in last_bound..=bound {
            for state in self.nfa.states() {
                let reach_var = self.reach_vars[&(state, l)];
                let mut alo_clause = clause!(nlit(reach_var));
                for (q_pred, trans) in self.delta_inv.get(&state).unwrap_or(&vec![]) {
                    let reach_prev = self.reach_vars[&(*q_pred, l - 1)];
                    // Tseitin on-the-fly
                    let def_var = pvar();
                    alo_clause.add(plit(def_var));
                    match trans {
                        TransitionType::Range(range) if range.is_full() => {
                            // Is predecessor if we do not read lambda
                            let sub_var = dom.string().get_sub(&self.var, l - 1, LAMBDA).unwrap();
                            // reach_prev /\ -sub_var
                            sink.add_binary(nlit(def_var), plit(reach_prev));
                            sink.add_binary(nlit(def_var), nlit(sub_var));
                        }
                        TransitionType::Range(range) if range.len() == 1 => {
                            // Is predecessor if we read the given character
                            let c = range.start();
                            let sub_var = dom.string().get_sub(&self.var, l - 1, c).unwrap();
                            sink.add_binary(nlit(def_var), plit(reach_prev));
                            sink.add_binary(nlit(def_var), plit(sub_var));
                        }
                        TransitionType::Range(range) => {
                            // Is predecessor if we read a character in the given range

                            // reach_prev /\ (sub_var_1 \/ ... \/ sub_var_n)
                            sink.add_binary(nlit(def_var), plit(reach_prev));

                            let mut range_clause = Clause::from([nlit(def_var)]);
                            for c in range.iter() {
                                let sub_var = dom.string().get_sub(&self.var, l - 1, c).unwrap();
                                range_clause.add(plit(sub_var));
                            }

                            sink.add_clause(range_clause);
                        }
                        TransitionType::NotRange(range) if range.len() == 1 => {
                            // Is predecessor if we **NOT** read the given character
                            let c = range.start();
                            let sub_var = dom.string().get_sub(&self.var, l - 1, c).unwrap();
                            sink.add_binary(nlit(def_var), plit(reach_prev));
                            sink.add_binary(nlit(def_var), nlit(sub_var));
                        }
                        TransitionType::NotRange(range) => {
                            // Is predecessor if we read a character in the given range

                            // reach_prev /\ (-sub_var_1 \/ ... \/ -sub_var_n)
                            sink.add_binary(nlit(def_var), plit(reach_prev));

                            let mut range_clause = Clause::from([nlit(def_var)]);
                            for c in range.iter() {
                                let sub_var = dom.string().get_sub(&self.var, l - 1, c).unwrap();
                                range_clause.add(nlit(sub_var));
                            }

                            sink.add_clause(range_clause);
                        }
                        TransitionType::Epsilon => {
                            return Err(EncodingError::not_epsi_free());
                        }
                    }
                }

                // Allow lambda self-transitions
                let reach_prev = self.reach_vars[&(state, l - 1)];
                let lambda_sub_var = dom.string().get_sub(&self.var, l - 1, LAMBDA).unwrap();
                let def_var = pvar();
                alo_clause.add(plit(def_var));
                sink.add_clause(Clause::from([nlit(def_var), plit(reach_prev)]));
                sink.add_clause(Clause::from([nlit(def_var), plit(lambda_sub_var)]));

                sink.add_clause(alo_clause);
            }
        }

        Ok(())
    }

    fn encode_final(&self, bound: usize, sink: &mut impl EncodingSink) {
        if self.sign {
            self.encode_final_positive(bound, sink)
        } else {
            self.encode_final_negative(bound, sink)
        }
    }

    fn encode_final_positive(&self, bound: usize, sink: &mut impl EncodingSink) {
        let selector = self.bound_selector.unwrap();

        let mut clause = clause![nlit(selector)];
        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(qf, bound)];
            clause.add(plit(reach_var));
        }
        sink.add_clause(clause);
    }

    fn encode_final_negative(&self, bound: usize, sink: &mut impl EncodingSink) {
        let selector = self.bound_selector.unwrap();

        for qf in self.nfa.finals() {
            let reach_var = self.reach_vars[&(qf, bound)];
            sink.add_clause(clause![nlit(selector), nlit(reach_var)]);
        }
    }
}

impl EncodeLiteral for NFAEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        self.last_bound = None;
        self.reach_vars.clear();
        self.bound_selector = None;
    }

    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let bound = dom
            .get_string(&self.var)
            .and_then(|i| i.upper_finite())
            .unwrap_or(0) as usize;

        log::trace!("Bound: {}", bound);
        if Some(bound) == self.last_bound {
            log::trace!("Upper bound did not change, skipping encoding");
            if let Some(s) = self.bound_selector {
                sink.add_assumption(plit(s));
                return Ok(());
            } else {
                return Ok(());
            }
        }

        // Create new selector for this bound
        let selector = pvar();
        self.bound_selector = Some(selector);
        sink.add_assumption(plit(selector));
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

        self.encode_intial(sink);

        self.encode_transitions(effective_bound, dom_enc, sink)?;

        self.encode_predecessor(effective_bound, dom_enc, sink)?;

        self.encode_final(effective_bound, sink);

        self.last_bound = Some(bound);
        Ok(())
    }
}

impl NFAEncoder {
    pub(super) fn new(var: Rc<Variable>, nfa: Rc<NFA>, pol: bool) -> Self {
        let delta_inv = precompute_delta_inv(&nfa).unwrap();
        Self {
            var: var,
            nfa,
            delta_inv,
            sign: pol,
            last_bound: None,
            reach_vars: IndexMap::new(),
            bound_selector: None,
        }
    }
}

impl From<StateNotFound> for EncodingError {
    fn from(err: StateNotFound) -> Self {
        EncodingError::new(&err.to_string())
    }
}

fn precompute_delta_inv(
    nfa: &Rc<NFA>,
) -> Result<IndexMap<StateId, Vec<(StateId, TransitionType)>>, StateNotFound> {
    let mut delta_inv = IndexMap::new();

    // Do one DFS
    if let Some(initial) = nfa.initial() {
        let mut stack = vec![initial];
        let mut visited = IndexSet::new();
        visited.insert(initial);

        while let Some(state) = stack.pop() {
            for transition in nfa.transitions_from(state)? {
                let dest = transition.get_dest();
                let entry = delta_inv.entry(dest).or_insert_with(Vec::new);

                entry.push((state, *transition.get_type()));
                if !visited.contains(&dest) {
                    stack.push(dest);
                    visited.insert(dest);
                }
            }
        }
    }
    Ok(delta_inv)
}

#[cfg(test)]
mod test {

    use rustsat::solvers::{Solve, SolveIncremental, SolverResult};
    use rustsat_cadical::CaDiCaL;
    use smt_str::re::Regex;

    use smallvec::smallvec;

    use super::*;

    use crate::{
        context::{Context, Sort},
        encode::{domain::DomainEncoder, EncodingResult, ResultSink},
        interval::Interval,
    };

    fn solve_with_bounds(re: Regex, pol: bool, ubounds: &[usize]) -> Option<SolverResult> {
        let mut ctx = Context::default();
        let var = ctx.temp_var(Sort::String);

        let alph = re.alphabet().as_ref().clone();
        let alph = Rc::new(alph);

        let nfa = ctx.get_nfa(&re);

        let mut bounds = Domain::default();

        let mut encoder = NFAEncoder::new(var.clone(), nfa, pol);
        let mut dom_encoder = DomainEncoder::new(alph);
        let mut solver = CaDiCaL::default();

        let mut result = None;
        for bound in ubounds {
            bounds.set_string(var.clone(), Interval::new(0, *bound as isize));
            let mut res = EncodingResult::empty();

            let mut sink = ResultSink::default();
            dom_encoder.encode(&bounds, &mut sink);

            encoder
                .encode(&bounds, dom_encoder.encoding(), &mut sink)
                .unwrap();
            res.extend(sink.result());

            match res {
                EncodingResult::Cnf(clauses, assms) => {
                    solver.add_cnf(clauses).unwrap();
                    let assm = assms.into_iter().collect::<Vec<_>>();
                    result = solver.solve_assumps(&assm).ok();
                    if let Some(rustsat::solvers::SolverResult::Sat) = result {
                        let _model = dom_encoder.encoding().get_model(&solver, &mut ctx);
                        let var_model = _model.get(&var).unwrap().as_str_const().unwrap();
                        assert!(
                            re.accepts(&var_model.clone()),
                            "Model `{}` does not match regex `{}`",
                            var_model,
                            re
                        );

                        return Some(rustsat::solvers::SolverResult::Sat);
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

        let re = ctx.re_builder().epsilon();

        assert_eq!(
            solve_with_bounds(re, true, &[1]),
            Some(rustsat::solvers::SolverResult::Sat)
        );
    }

    #[test]
    fn var_in_none() {
        let mut ctx = Context::default();

        let re = ctx.re_builder().none();

        assert_eq!(
            solve_with_bounds(re, true, &[10]),
            Some(rustsat::solvers::SolverResult::Unsat)
        );
    }

    #[test]
    fn var_in_const_no_concat() {
        let mut ctx = Context::default();

        let re = ctx.re_builder().to_re("foo".into());

        assert_eq!(
            solve_with_bounds(re, true, &[7]),
            Some(rustsat::solvers::SolverResult::Sat)
        );
    }

    #[test]
    fn var_in_const_concat() {
        let mut ctx = Context::default();

        let builder = ctx.re_builder();

        let args = smallvec![builder.to_re("foo".into()), builder.to_re("bar".into())];
        let re = builder.concat(args);

        assert_eq!(
            solve_with_bounds(re, true, &[10]),
            Some(rustsat::solvers::SolverResult::Sat)
        );
    }
}
