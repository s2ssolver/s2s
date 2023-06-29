use std::collections::HashMap;

use crate::bounds::Bounds;
use crate::encode::card::exactly_one;
use crate::encode::domain::DomainEncoding;
use crate::encode::{ConstraintEncoder, EncodingResult, FilledPattern, FilledPos, LAMBDA};

use crate::error::Error;
use crate::model::constraints::WordEquation;
use crate::sat::{as_lit, neg, pvar, Cnf, PVar};
use indexmap::IndexSet;

use super::WordEquationEncoder;

/// The incremental version of the Woorpje encoding.
pub struct IWoorpjeEncoder {
    /// The original word equation
    equation: WordEquation,

    /// The filled equation, used to encode in the current round. None prior to the first round.
    filled_equation: Option<(FilledPattern, FilledPattern)>,

    /// The last filled equation, used to encode in the last round. Is `None` if this is the first round.
    previous_filled_equation: Option<(FilledPattern, FilledPattern)>,

    /// The variables that encode the states of the matching automaton
    state_vars: Vec<Vec<PVar>>,

    /// The substitution encoding of the left-hand side. Maps a positions and a character to a variable that is true if the character is at the position.
    subs_lhs: HashMap<(usize, char), PVar>,
    /// The substitution encoding of the right-hand side. Maps a positions and a character to a variable that is true if the character is at the position.
    subs_rhs: HashMap<(usize, char), PVar>,

    /// The selector variable used in the previous round. Is `None` if this is the first round.
    selector: Option<PVar>,

    /// Counts the rounds, is 0 prior to the first round and is incremented each call to `encode`.
    round: usize,
}

impl IWoorpjeEncoder {
    /// Returns the length of the pattern in the previous round.
    /// Is (0, 0) is the first round.
    fn prev_lens(&self) -> (usize, usize) {
        self.previous_filled_equation
            .as_ref()
            .map(|(lhs, rhs)| (lhs.length(), rhs.length()))
            .unwrap_or((0, 0))
    }

    /// Returns the length of the pattern in this round.
    /// Is (0, 0) is prior to first round.
    fn lens(&self) -> (usize, usize) {
        self.filled_equation
            .as_ref()
            .map(|(lhs, rhs)| (lhs.length(), rhs.length()))
            .unwrap_or((0, 0))
    }

    fn update_pattern(&mut self, dom: &DomainEncoding) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (prev_len_lhs, prev_len_rhs) = self.prev_lens();
        let (lhs, rhs) = self.filled_equation.as_ref().unwrap();
        assert!(
            prev_len_lhs <= lhs.length(),
            "Pattern shrinking: {} > {}",
            prev_len_lhs,
            lhs.length(),
        );
        assert!(
            prev_len_rhs <= rhs.length(),
            "Pattern shrinking: {} > {}",
            prev_len_rhs,
            lhs.length(),
        );

        // Left-hand side
        for i in prev_len_lhs..lhs.length() {
            let mut choices = Vec::new();
            for c in dom.alphabet_lambda() {
                let v = pvar();
                choices.push(v);
                self.subs_lhs.insert((i, c), v);
            }
            cnf.extend(exactly_one(&choices));
        }
        // Right-hand side
        for i in prev_len_rhs..rhs.length() {
            let mut choices = Vec::new();
            for c in dom.alphabet_lambda() {
                let v = pvar();
                choices.push(v);
                self.subs_rhs.insert((i, c), v);
            }
            cnf.extend(exactly_one(&choices));
        }
        assert_eq!(
            self.subs_lhs.len(),
            lhs.length() * dom.alphabet_lambda().len()
        );
        assert_eq!(
            self.subs_rhs.len(),
            rhs.length() * dom.alphabet_lambda().len()
        );
        EncodingResult::cnf(cnf)
    }

    fn align_pattern(&mut self, dom: &DomainEncoding) -> EncodingResult {
        let mut assms = IndexSet::new();
        let mut cnf = Cnf::new();
        let subs = dom.string();
        let (lhs, rhs) = self.filled_equation.as_ref().unwrap();

        let selector = pvar();
        self.selector = Some(selector);
        let selector = as_lit(selector);
        assms.insert(selector);
        // Left-hand side
        for i in 0..lhs.length() {
            match &lhs[i] {
                FilledPos::Const(c) => {
                    assms.insert(as_lit(self.subs_lhs[&(i, *c)]));
                    assms.insert(neg(self.subs_lhs[&(i, LAMBDA)]));
                }
                FilledPos::FilledPos(v, j) => {
                    for c in dom.alphabet_lambda() {
                        let sub_p = as_lit(self.subs_lhs[&(i, c)]);
                        let sub_x = as_lit(
                            subs.get(v, *j, c)
                                .unwrap_or_else(|| panic!("{:?}[{}] = {} not defined", v, j, c)),
                        );
                        // selector -> (sub_p <-> sub_x)
                        // <=> selector -> (sub_p -> sub_x) /\ selector -> (sub_x -> sub_p)
                        // <=> (-selector \/ -sub_p \/ sub_x) /\ (-selector \/ -sub_x \/ sub_p)
                        cnf.push(vec![-selector, -sub_p, sub_x]);
                        cnf.push(vec![-selector, sub_p, -sub_x]);
                    }
                }
            }
        }
        // Right-hand side
        for i in 0..rhs.length() {
            match &rhs[i] {
                FilledPos::Const(c) => {
                    assms.insert(as_lit(self.subs_rhs[&(i, *c)]));
                    assms.insert(neg(self.subs_rhs[&(i, LAMBDA)]));
                }
                FilledPos::FilledPos(v, j) => {
                    for c in dom.alphabet_lambda() {
                        let sub_p = as_lit(self.subs_rhs[&(i, c)]);
                        let sub_x = as_lit(subs.get(v, *j, c).unwrap());
                        // see above
                        cnf.push(vec![-selector, -sub_p, sub_x]);
                        cnf.push(vec![-selector, sub_p, -sub_x]);
                    }
                }
            }
        }

        for i in 0..lhs.length() {
            for j in i + 1..rhs.length() {
                if let FilledPos::FilledPos(v, k) = &lhs[i] {
                    if let FilledPos::FilledPos(w, l) = &rhs[j] {
                        if v == w && l == k {
                            for c in dom.alphabet_lambda() {
                                let sub_lhs = as_lit(self.subs_lhs[&(i, c)]);
                                let sub_rhs = as_lit(self.subs_rhs[&(j, c)]);
                                // selector -> (sub_lhs <-> sub_rhs)
                                // <=> selector -> (sub_lhs -> sub_rhs) /\ selector -> (sub_rhs -> sub_lhs)
                                // <=> (-selector \/ -sub_lhs \/ sub_rhs) /\ (-selector \/ -sub_rhs \/ sub_lhs)
                                cnf.push(vec![-selector, -sub_lhs, sub_rhs]);
                                cnf.push(vec![-selector, sub_lhs, -sub_rhs]);
                            }
                        }
                    }
                }
            }
        }

        log::trace!("Selected: {}", cnf.len());
        EncodingResult::Cnf(cnf, assms)
    }

    fn update_state_vars(&mut self) -> EncodingResult {
        let n_old = self.state_vars.len();
        let (n_new, m_new) = self.lens();
        let n_new = n_new + 2;
        let m_new = m_new + 2;

        for i in 0..n_new {
            if i < n_old {
                // Extend existing row
                for _ in self.state_vars[i].len()..m_new {
                    self.state_vars[i].push(pvar());
                }
            } else {
                // Add new row
                let mut row = Vec::new();
                for _ in 0..m_new {
                    row.push(pvar());
                }
                self.state_vars.push(row);
            }
        }

        assert_eq!(n_new, self.state_vars.len());
        assert_eq!(m_new, self.state_vars[0].len());
        assert!(self.state_vars[n_new - 1][m_new - 1] > 0);

        // These states are not allowed in the current round, we disallow them with assumptions
        let xborder = self.state_vars.len() - 1;
        let yborder = self.state_vars[0].len() - 1;
        let mut disallowed = IndexSet::new();
        for i in 0..self.state_vars.len() {
            disallowed.insert(neg(self.state_vars[i][yborder]));
        }
        for j in 0..self.state_vars[0].len() {
            disallowed.insert(neg(self.state_vars[xborder][j]));
        }

        EncodingResult::Cnf(vec![], disallowed)
    }

    #[allow(unused)]
    pub fn get_selector(&self) -> Option<PVar> {
        self.selector
    }

    fn encode_successors(&mut self, i: usize, j: usize) -> EncodingResult {
        let mut cnf = Cnf::new();
        let assm = IndexSet::new();
        let (n_last, m_last) = self.prev_lens();
        let (n, m) = self.lens();

        #[allow(clippy::nonminimal_bool)]
        if (i < n_last && j < m_last) || (i < n_last && j == m_last) || (i == n_last && j < m_last)
        {
            // Skip states that are not in the current round
            // Does not skip (n_last, m_last), which now has successors
            return EncodingResult::Trivial(true);
        }

        if i == n && j == m {
            // Last state does not need to have successors in this round
            // Will be handled by the next round, if necessary
            return EncodingResult::empty();
        }
        let s_00 = self.state_vars[i][j];
        let s_01 = self.state_vars[i][j + 1];
        let s_10 = self.state_vars[i + 1][j];
        let s_11 = self.state_vars[i + 1][j + 1];
        let clause = vec![neg(s_00), as_lit(s_01), as_lit(s_10), as_lit(s_11)];

        cnf.push(clause);

        // At most one successor
        cnf.push(vec![neg(s_00), neg(s_01), neg(s_10)]);
        cnf.push(vec![neg(s_00), neg(s_01), neg(s_11)]);

        cnf.push(vec![neg(s_00), neg(s_10), neg(s_01)]);
        cnf.push(vec![neg(s_00), neg(s_10), neg(s_11)]);

        cnf.push(vec![neg(s_00), neg(s_11), neg(s_01)]);
        cnf.push(vec![neg(s_00), neg(s_11), neg(s_10)]);

        EncodingResult::Cnf(cnf, assm)
    }

    fn encode_move_right(&mut self, i: usize, j: usize) -> EncodingResult {
        let mut cnf = Cnf::with_capacity(2);
        let s_00 = self.state_vars[i][j];

        if j < self.lens().1 {
            let s_01 = self.state_vars[i][j + 1];
            let rhs_lambda = self.subs_rhs.get(&(j, LAMBDA)).unwrap();

            // i < n' && j < m': All encoded in previous round

            // i == n' && j < m': i is on previous margin => encode that lhs[i] must not be lambda if going rightwards
            if i == self.prev_lens().0
                && j < self.prev_lens().1
                && self.prev_lens().0 < self.lens().0
            {
                let lhs_lambda = self.subs_lhs.get(&(i, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_01), neg(*lhs_lambda)]);
                cnf.push(vec![
                    neg(*rhs_lambda),
                    as_lit(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_01),
                ])
            }

            // j < m' && i > n' && i < n: Encode rhs[j] must be lambda and lhs[i] must not be lambda
            if j < self.prev_lens().1 && i > self.prev_lens().0 && i < self.lens().0 {
                let lhs_lambda = self.subs_lhs.get(&(i, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_01), as_lit(*rhs_lambda)]);
                cnf.push(vec![neg(s_00), neg(s_01), neg(*lhs_lambda)]);

                cnf.push(vec![
                    neg(*rhs_lambda),
                    as_lit(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_01),
                ])
            }

            // j >= m' && i < n: Encode rhs[j] must be lambda and lhs[i] must not be lambda
            if j >= self.prev_lens().1 && i < self.lens().0 {
                let lhs_lambda = self.subs_lhs.get(&(i, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_01), as_lit(*rhs_lambda)]);
                cnf.push(vec![neg(s_00), neg(s_01), neg(*lhs_lambda)]);
                cnf.push(vec![
                    neg(*rhs_lambda),
                    as_lit(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_01),
                ])
            }

            // j >=m' && i==n: i is on current margin, encode that rhs[j] must be lambda if going rightwards
            if j >= self.prev_lens().1 && i == self.lens().0 {
                cnf.push(vec![neg(s_00), neg(s_01), as_lit(*rhs_lambda)]);
                let s = *self.selector.as_ref().unwrap();
                cnf.push(vec![neg(s), neg(*rhs_lambda), neg(s_00), as_lit(s_01)]);
            }
        }

        EncodingResult::cnf(cnf)
    }

    fn encode_move_down(&mut self, i: usize, j: usize) -> EncodingResult {
        let mut cnf = Cnf::with_capacity(2);
        let s_00 = self.state_vars[i][j];

        if i < self.lens().0 {
            let s_10 = self.state_vars[i + 1][j];
            let lhs_lambda = self.subs_lhs.get(&(i, LAMBDA)).unwrap();

            // i < n' && j < m': All encoded in previous round

            // i < n' && j == m': j is on previous margin => encode that rhs[j] must not be lambda if going downwards
            if i < self.prev_lens().0
                && j == self.prev_lens().1
                && self.prev_lens().1 < self.lens().1
            {
                let rhs_lambda = self.subs_rhs.get(&(j, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_10), neg(*rhs_lambda)]);
                cnf.push(vec![
                    as_lit(*rhs_lambda),
                    neg(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_10),
                ])
            }

            // i < n' && j > m' && j < m: Encode lhs[i] must be lambda and rhs[j] must not be lambda
            if i < self.prev_lens().0 && j > self.prev_lens().1 && j < self.lens().1 {
                let rhs_lambda = self.subs_rhs.get(&(j, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_10), as_lit(*lhs_lambda)]);
                cnf.push(vec![neg(s_00), neg(s_10), neg(*rhs_lambda)]);
                cnf.push(vec![
                    as_lit(*rhs_lambda),
                    neg(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_10),
                ])
            }
            // i >= n && j < m: Encode lhs[i] must be lambda and rhs[j] must not be lambda
            if i >= self.prev_lens().0 && j < self.lens().1 {
                let rhs_lambda = self.subs_rhs.get(&(j, LAMBDA)).unwrap();
                cnf.push(vec![neg(s_00), neg(s_10), as_lit(*lhs_lambda)]);
                cnf.push(vec![neg(s_00), neg(s_10), neg(*rhs_lambda)]);
                cnf.push(vec![
                    as_lit(*rhs_lambda),
                    neg(*lhs_lambda),
                    neg(s_00),
                    as_lit(s_10),
                ])
            }
            // i >= n && j == m: j is on current margin, encode that lhs[i] must be lambda if going downwards
            if i >= self.prev_lens().0 && j == self.lens().1 {
                cnf.push(vec![neg(s_00), neg(s_10), as_lit(*lhs_lambda)]);
                let s = self.selector.unwrap();
                cnf.push(vec![neg(s), neg(*lhs_lambda), neg(s_00), as_lit(s_10)]);
            }
        }

        EncodingResult::cnf(cnf)
    }

    fn encode_move_forward(&mut self, i: usize, j: usize, dom: &DomainEncoding) -> EncodingResult {
        let mut cnf = Cnf::with_capacity(2);
        let s_00 = self.state_vars[i][j];
        let s_11 = self.state_vars[i + 1][j + 1];

        if i < self.lens().0
            && j < self.lens().1
            && (j >= self.prev_lens().1 || i >= self.prev_lens().0)
        {
            for c in dom.alphabet_lambda() {
                let lhs_sub = self.subs_lhs.get(&(i, c)).unwrap();
                let rhs_sub = self.subs_rhs.get(&(j, c)).unwrap();

                cnf.push(vec![neg(s_00), neg(s_11), neg(*lhs_sub), as_lit(*rhs_sub)]);

                cnf.push(vec![neg(*lhs_sub), neg(*rhs_sub), neg(s_00), as_lit(s_11)])
            }

            let lhs_lambda = *self.subs_lhs.get(&(i, LAMBDA)).unwrap();
            let rhs_lambda = *self.subs_rhs.get(&(j, LAMBDA)).unwrap();

            cnf.push(vec![
                neg(s_00),
                neg(lhs_lambda),
                as_lit(rhs_lambda),
                neg(s_11),
            ]);
            cnf.push(vec![
                neg(s_00),
                as_lit(lhs_lambda),
                neg(rhs_lambda),
                neg(s_11),
            ]);
        }
        EncodingResult::cnf(cnf)
    }

    fn encode_moves(&mut self, i: usize, j: usize, dom: &DomainEncoding) -> EncodingResult {
        let mut res = EncodingResult::empty();

        res.join(self.encode_move_right(i, j));

        res.join(self.encode_move_down(i, j));

        res.join(self.encode_move_forward(i, j, dom));

        res
    }

    fn encode_valid(&mut self, dom: &DomainEncoding, i: usize, j: usize) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let (n_last, m_last) = self.prev_lens();
        if i < n_last && j < m_last {
            // Already encoded
            return res;
        }
        res.join(self.encode_moves(i, j, dom));

        res
    }

    /*  fn guide(&mut self, subs: &SubstitutionEncoding) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (n, m) = self.last_len;
        for i in 0..self.state_vars.len() {
            for j in 0..self.state_vars[i].len() {
                if i < n && j < m {
                    // Already encoded
                    continue;
                }
                let s_00 = as_lit(self.state_vars[i][j]);

                // State deactivation

                // Lambda transitions if
                if i < self.state_vars.len() - 2 {
                    let sub = self.subs_lhs.get(&(i, LAMBDA)).unwrap();
                    let succ = self.state_vars[i + 1][j];
                    cnf.push(vec![-s_00, as_lit(*sub), neg(succ)]);
                }
                if j < self.state_vars[i].len() - 2 {
                    let sub = self.subs_rhs.get(&(j, LAMBDA)).unwrap();
                    let succ = self.state_vars[i][j + 1];
                    cnf.push(vec![-s_00, as_lit(*sub), neg(succ)]);
                }
                // Lamda transitions if 2
                if i < self.state_vars.len() - 2 && j < self.state_vars[i].len() - 2 {
                    let sub_l = self.subs_lhs[&(i, LAMBDA)];
                    let sub_r = self.subs_rhs[&(j, LAMBDA)];
                    let succ_01 = self.state_vars[i][j + 1];
                    let succ_10 = self.state_vars[i + 1][j];
                    cnf.push(vec![-s_00, as_lit(sub_l), neg(sub_r), as_lit(succ_01)]);
                    cnf.push(vec![-s_00, neg(sub_l), as_lit(sub_r), as_lit(succ_10)]);
                }

                // At most one successor
                if i < self.state_vars.len() - 2 && j < self.state_vars[i].len() - 2 {
                    let s_10 = as_lit(self.state_vars[i + 1][j]);
                    let s_01 = as_lit(self.state_vars[i][j + 1]);
                    let s_11 = as_lit(self.state_vars[i + 1][j + 1]);

                    // 2. At most one successor state (a)
                    cnf.push(vec![-s_00, -s_01, -s_11]); // s_00 /\ s_01 --> -s_11
                    cnf.push(vec![-s_00, -s_01, -s_10]); // s_00 /\ s_01 --> -s_10

                    // 3. At most one successor state (b)
                    cnf.push(vec![-s_00, -s_10, -s_11]); // s_00 /\ s_10 --> -s_11
                    cnf.push(vec![-s_00, -s_10, -s_01]); // s_00 /\ s_10 --> -s_01

                    // 4. At most one successor state (c)
                    cnf.push(vec![-s_00, -s_11, -s_10]); // s_00 /\ s_11 --> -s_10
                    cnf.push(vec![-s_00, -s_11, -s_01]); // s_00 /\ s_11 --> -s_01
                }
            }
        }
        EncodingResult::cnf(cnf)
    }*/

    /// Returns the state variables of the pattern matching automaton.
    #[allow(unused)]
    fn get_state_vars(&self) -> &Vec<Vec<PVar>> {
        &self.state_vars
    }

    fn encode_initial_state(&self) -> EncodingResult {
        if self.prev_lens() == (0, 0) {
            EncodingResult::cnf(vec![vec![as_lit(self.state_vars[0][0])]])
        } else {
            EncodingResult::Trivial(true)
        }
    }

    fn encode_accepting_state(&self) -> EncodingResult {
        let (n, m) = self.lens();
        EncodingResult::assumption(as_lit(self.state_vars[n][m]))
    }
}

impl WordEquationEncoder for IWoorpjeEncoder {
    fn new(equation: WordEquation, sing: bool) -> Self {
        if !sing {
            panic!("IWoorpjeEncoder does not support inequalities")
        }
        Self {
            state_vars: Vec::new(),
            equation,
            subs_lhs: HashMap::new(),
            subs_rhs: HashMap::new(),
            filled_equation: None,
            previous_filled_equation: None,
            selector: None,
            round: 0,
        }
    }
}

impl ConstraintEncoder for IWoorpjeEncoder {
    fn encode(&mut self, bounds: &Bounds, dom: &DomainEncoding) -> Result<EncodingResult, Error> {
        self.round += 1;
        let mut res = if let Some(old_selector) = self.selector {
            EncodingResult::assumption(neg(old_selector))
        } else {
            EncodingResult::empty()
        };
        let lhs = FilledPattern::fill(self.equation.lhs(), bounds);
        let rhs = FilledPattern::fill(self.equation.rhs(), bounds);
        let prev = self.filled_equation.take();
        self.previous_filled_equation = prev;
        self.filled_equation = Some((lhs, rhs));
        // TODO: Check if (lhs.len, rhs.len) == last_len and return assumptions from last call

        res.join(self.update_state_vars());
        res.join(self.update_pattern(dom));
        res.join(self.align_pattern(dom));

        let (n, m) = self.lens();
        for i in 0..=n {
            for j in 0..=m {
                res.join(self.encode_successors(i, j));
                res.join(self.encode_valid(dom, i, j));
            }
        }

        res.join(self.encode_initial_state());
        res.join(self.encode_accepting_state());
        //res.join(self.guide(substitution));
        //self.check();
        Ok(res)
    }

    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        let new = Self::new(self.equation.clone(), true);
        // Reset everything except the equation
        *self = new;
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use cadical::Solver;

    use crate::{
        bounds::IntDomain,
        encode::domain::{get_substitutions, DomainEncoder},
        instance::Instance,
        model::{constraints::Pattern, Evaluable, Sort, Substitutable, Substitution, Variable},
    };

    fn solve_iwoorpje(
        eq: &WordEquation,
        bounds: Bounds,
        alphabet: &IndexSet<char>,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();
        let mut instance = Instance::default();
        eq.variables().iter().for_each(|v| {
            instance.add_var(v.clone());
        });
        let mut dom_encoder = DomainEncoder::new(alphabet.clone());

        let subs_cnf = dom_encoder.encode(&bounds, &instance);

        encoding.join(subs_cnf);
        let mut encoder = IWoorpjeEncoder::new(eq.clone(), true);
        encoding.join(encoder.encode(&bounds, dom_encoder.encoding()).unwrap());

        let mut solver: Solver = Solver::default();
        let mut assumptions = HashSet::new();
        match encoding {
            EncodingResult::Cnf(cnf, assms) => {
                for clause in cnf {
                    solver.add_clause(clause);
                }
                assumptions.extend(assms);
            }
            EncodingResult::Trivial(false) => return Some(false),
            EncodingResult::Trivial(true) => return Some(true),
        }
        let res = solver.solve_with(assumptions.into_iter());
        if let Some(true) = res {
            let solution = get_substitutions(dom_encoder.encoding(), &instance, &solver);
            let solution = Substitution::from(solution);
            assert!(
                eq.eval(&solution).unwrap(),
                "{} is not a solution: {:?} != {:?}",
                solution,
                eq.lhs().apply_substitution(&solution),
                eq.rhs().apply_substitution(&solution)
            );
        }
        res
    }

    fn solve_iwoorpje_incremental(
        eq: &WordEquation,
        limit: usize,
        alphabet: &IndexSet<char>,
    ) -> Option<bool> {
        let mut bounds = Bounds::with_defaults(IntDomain::Bounded(0, 1));

        let mut encoder = IWoorpjeEncoder::new(eq.clone(), true);
        let mut instance = Instance::default();
        eq.variables().iter().for_each(|v| {
            instance.add_var(v.clone());
        });
        let mut dom_encoder = DomainEncoder::new(alphabet.clone());

        let mut result = None;
        let mut done = !bounds.uppers_leq(limit as isize);
        let mut solver: cadical::Solver = cadical::Solver::new();
        while !done {
            let mut encoding = EncodingResult::empty();

            encoding.join(dom_encoder.encode(&bounds, &instance));
            encoding.join(encoder.encode(&bounds, dom_encoder.encoding()).unwrap());
            result = match encoding {
                EncodingResult::Cnf(cnf, assm) => {
                    for clause in cnf {
                        solver.add_clause(clause);
                    }
                    solver.solve_with(assm.into_iter())
                }
                EncodingResult::Trivial(f) => Some(f),
            };
            // Limit reached
            done = bounds.uppers_geq(limit as isize);

            bounds.next_square_uppers();
            bounds.clamp_uppers(limit as isize);
        }
        match result {
            Some(true) => {
                let sol = get_substitutions(dom_encoder.encoding(), &instance, &solver);
                let solution = Substitution::from(sol);

                assert!(
                    eq.eval(&solution).unwrap(),
                    "Not a solution: {} ({})",
                    solution,
                    eq
                );
            }

            _ => {}
        }
        result
    }

    #[test]
    fn iwoorpje_incremental_sat() {
        let eq = WordEquation::parse_simple("abc", "X");
        let res = solve_iwoorpje_incremental(&eq, 10, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_empty_eq() {
        let eq = WordEquation::new(Pattern::from(vec![]), Pattern::from(vec![]));
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_sat_consts() {
        let eq = WordEquation::constant("bar", "bar");
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_unsat_consts() {
        let eq = WordEquation::constant("bar", "barr");
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn iwoorpje_trivial_sat_const_var() {
        let eq = WordEquation::parse_simple("X", "bar");

        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 5));

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_sat_vars() {
        let var = Pattern::variable(&Variable::temp(Sort::String));
        let eq = WordEquation::new(var.clone(), var);
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_sat_commute() {
        // AB = BA
        let var_a = Variable::temp(Sort::String);
        let var_b = Variable::temp(Sort::String);
        let mut lhs = Pattern::empty();
        lhs.append_var(&var_a).append_var(&var_b);
        let mut rhs = Pattern::empty();
        rhs.append_var(&var_b).append_var(&var_a);
        let eq = WordEquation::new(lhs, rhs);
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_sat_pattern_const() {
        let eq = WordEquation::parse_simple("aXc", "abc");
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 1));
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_test() {
        let eq = WordEquation::parse_simple("aXb", "YXb");
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 3));
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_unsat_const_var_too_small() {
        let eq = WordEquation::new(
            Pattern::constant("foo"),
            Pattern::variable(&Variable::temp(Sort::String)),
        );

        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 1));

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn iwoorpje_sat_t1i74() {
        let eq = WordEquation::parse_simple("A", "dFg");

        let res = solve_iwoorpje_incremental(&eq, 4, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
}
