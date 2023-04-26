use std::collections::{HashMap, HashSet};

use crate::encode::card::exactly_one;
use crate::encode::substitution::SubstitutionEncoding;
use crate::encode::{
    EncodingResult, FilledPattern, FilledPos, PredicateEncoder, VariableBounds, LAMBDA,
};
use crate::model::words::WordEquation;
use crate::sat::{as_lit, neg, pvar, Cnf, PVar};

use super::WordEquationEncoder;

pub struct IWoorpjeEncoder {
    equation: WordEquation,
    state_vars: Vec<Vec<PVar>>,
    // The pattern encoding of the left-hand side
    pat_lhs: HashMap<(usize, char), PVar>,
    // The pattern encoding of the right-hand side
    pat_rhs: HashMap<(usize, char), PVar>,
    last_len: (usize, usize),
}

impl IWoorpjeEncoder {
    fn update_pattern(
        &mut self,
        lhs: &FilledPattern,
        rhs: &FilledPattern,
        subs: &SubstitutionEncoding,
    ) -> EncodingResult {
        let mut cnf = Cnf::new();
        assert!(
            self.last_len.0 <= lhs.length(),
            "Pattern shrinking: {} <= {}",
            lhs.length(),
            self.last_len.0
        );
        assert!(
            self.last_len.1 <= rhs.length(),
            "Pattern shrinking: {} <= {}",
            lhs.length(),
            self.last_len.0
        );

        // Left-hand side
        for i in self.last_len.0..lhs.length() {
            let mut choices = Vec::new();
            for c in subs.alphabet_lambda() {
                let v = pvar();
                choices.push(v);
                self.pat_lhs.insert((i, c), v);
            }
            cnf.extend(exactly_one(&choices));
        }
        // Right-hand side
        for i in self.last_len.1..rhs.length() {
            let mut choices = Vec::new();
            for c in subs.alphabet_lambda() {
                let v = pvar();
                choices.push(v);
                self.pat_rhs.insert((i, c), v);
            }
            cnf.extend(exactly_one(&choices));
        }
        assert_eq!(
            self.pat_lhs.len(),
            lhs.length() * subs.alphabet_lambda().len()
        );
        assert_eq!(
            self.pat_rhs.len(),
            rhs.length() * subs.alphabet_lambda().len()
        );
        EncodingResult::cnf(cnf)
    }

    fn align_patter(
        &self,
        lhs: &FilledPattern,
        rhs: &FilledPattern,
        subs: &SubstitutionEncoding,
    ) -> EncodingResult {
        let mut assms = HashSet::new();
        let mut cnf = Cnf::new();
        let selector = as_lit(pvar());
        assms.insert(selector);
        // Left-hand side
        for i in 0..lhs.length() {
            match &lhs[i] {
                FilledPos::Const(c) => {
                    assms.insert(as_lit(self.pat_lhs[&(i, *c)]));
                }
                FilledPos::FilledPos(v, j) => {
                    for c in subs.alphabet_lambda() {
                        let sub_p = as_lit(self.pat_lhs[&(i, c)]);
                        let sub_x = as_lit(subs.get(&v, *j, c).unwrap());
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
                    assms.insert(as_lit(self.pat_rhs[&(i, *c)]));
                }
                FilledPos::FilledPos(v, j) => {
                    for c in subs.alphabet_lambda() {
                        let sub_p = as_lit(self.pat_rhs[&(i, c)]);
                        let sub_x = as_lit(subs.get(&v, *j, c).unwrap());
                        // see above
                        cnf.push(vec![-selector, -sub_p, sub_x]);
                        cnf.push(vec![-selector, sub_p, -sub_x]);
                    }
                }
            }
        }
        EncodingResult::Cnf(cnf, assms)
    }

    fn update_state_vars(&mut self, u_size: usize, v_size: usize) -> EncodingResult {
        let n_old = self.state_vars.len();

        for i in 0..u_size + 2 {
            if i < n_old {
                // Extend existing row
                for _ in self.state_vars[i].len()..v_size + 2 {
                    self.state_vars[i].push(pvar());
                }
            } else {
                // Add new row
                let mut row = Vec::new();
                for _ in 0..v_size + 2 {
                    row.push(pvar());
                }
                self.state_vars.push(row);
            }
        }

        assert_eq!(u_size + 2, self.state_vars.len());
        assert_eq!(v_size + 2, self.state_vars[0].len());

        let xborder = self.state_vars.len() - 1;
        let yborder = self.state_vars[0].len() - 1;
        let mut disallowed = HashSet::new();
        for i in 0..self.state_vars.len() {
            disallowed.insert(neg(self.state_vars[i][yborder]));
        }
        for j in 0..self.state_vars[0].len() {
            disallowed.insert(neg(self.state_vars[xborder][j]));
        }

        EncodingResult::Cnf(vec![], disallowed)
    }

    fn encode_successors(&mut self) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (n, m) = self.last_len;
        // Todo: Do in one loop
        for i in n..self.state_vars.len() - 1 {
            for j in m..self.state_vars[i].len() - 1 {
                if i == self.state_vars.len() - 2 && j == self.state_vars[i].len() - 2 {
                    // Last cell does not have successors (yet)
                    continue;
                }
                let s_00 = as_lit(self.state_vars[i][j]);
                let s_01 = as_lit(self.state_vars[i][j + 1]);
                let s_10 = as_lit(self.state_vars[i + 1][j]);
                let s_11 = as_lit(self.state_vars[i + 1][j + 1]);

                cnf.push(vec![-s_00, s_01, s_10, s_11]);
            }
        }
        // Last cell from previous iteration needs successors now
        if self.last_len != (0, 0) {
            cnf.push(vec![
                neg(self.state_vars[self.last_len.0][self.last_len.1]),
                as_lit(self.state_vars[self.last_len.0 + 1][self.last_len.1]),
                as_lit(self.state_vars[self.last_len.0][self.last_len.1 + 1]),
                as_lit(self.state_vars[self.last_len.0 + 1][self.last_len.1 + 1]),
            ]);
        }
        EncodingResult::cnf(cnf)
    }

    fn encode_predecessors(&mut self) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (mut n, mut m) = self.last_len;

        // +1 will lead to one redundant encoding of the predecessor of the bot right cell from the previous iteration
        n += 1;
        m += 1;

        for i in 1..self.state_vars.len() {
            for j in 1..self.state_vars[i].len() {
                if i < n && j < m {
                    // Already encoded
                    continue;
                }
                let s_00 = as_lit(self.state_vars[i][j]);
                let s_01 = as_lit(self.state_vars[i][j - 1]);
                let s_10 = as_lit(self.state_vars[i - 1][j]);
                let s_11 = as_lit(self.state_vars[i - 1][j - 1]);

                cnf.push(vec![-s_00, s_01, s_10, s_11]);
            }
        }
        for i in n..self.state_vars.len() {
            let s_00 = as_lit(self.state_vars[i][0]);
            let s_10 = as_lit(self.state_vars[i - 1][0]);

            cnf.push(vec![-s_00, s_10]);
        }
        for j in m..self.state_vars[0].len() {
            let s_00 = as_lit(self.state_vars[0][j]);
            let s_01 = as_lit(self.state_vars[0][j - 1]);

            cnf.push(vec![-s_00, s_01]);
        }
        EncodingResult::cnf(cnf)
    }

    fn encode_transitions(&mut self, subs: &SubstitutionEncoding) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (mut n, mut m) = self.last_len;

        for i in 0..self.state_vars.len() {
            for j in 0..self.state_vars[i].len() {
                if i < n && j < m {
                    // Already encoded
                    continue;
                }
                let s_00 = as_lit(self.state_vars[i][j]);
                if i < self.state_vars.len() - 2 && j < self.state_vars[i].len() - 2 {
                    let s_01 = as_lit(self.state_vars[i][j + 1]);
                    let s_10 = as_lit(self.state_vars[i + 1][j]);
                    let s_11 = as_lit(self.state_vars[i + 1][j + 1]);
                    cnf.push(vec![-s_00, -s_10, as_lit(self.pat_lhs[&(i, LAMBDA)])]);
                    cnf.push(vec![-s_00, -s_01, as_lit(self.pat_rhs[&(j, LAMBDA)])]);
                    for c in subs.alphabet_lambda() {
                        let sub_l = self.pat_lhs[&(i, c)];
                        let sub_r = self.pat_rhs[&(j, c)];
                        cnf.push(vec![-s_00, -s_11, neg(sub_l), as_lit(sub_r)])
                    }
                } else if i < self.state_vars.len() - 2 && j == self.state_vars[i].len() - 2 {
                    let s_10 = as_lit(self.state_vars[i + 1][j]);
                    cnf.push(vec![-s_00, -s_10, as_lit(self.pat_lhs[&(i, LAMBDA)])]);
                } else if i == self.state_vars.len() - 2 && j < self.state_vars[i].len() - 2 {
                    let s_01 = as_lit(self.state_vars[i][j + 1]);
                    cnf.push(vec![-s_00, -s_01, as_lit(self.pat_rhs[&(j, LAMBDA)])]);
                }
            }
        }

        EncodingResult::cnf(cnf)
    }

    /// Returns the state variables of the pattern matching automaton.
    fn get_state_vars(&self) -> &Vec<Vec<PVar>> {
        &self.state_vars
    }

    fn encode_initial_state(&self) -> EncodingResult {
        if self.last_len == (0, 0) {
            EncodingResult::cnf(vec![vec![as_lit(self.state_vars[0][0])]])
        } else {
            EncodingResult::Trivial(true)
        }
    }

    fn encode_accepting_state(&self) -> EncodingResult {
        let n = self.state_vars.len() - 2;
        let m = self.state_vars[n].len() - 2;

        EncodingResult::assumption(as_lit(self.state_vars[n][m]))
    }
}

impl WordEquationEncoder for IWoorpjeEncoder {
    fn new(equation: WordEquation) -> Self {
        Self {
            state_vars: Vec::new(),
            equation: equation,
            pat_lhs: HashMap::new(),
            pat_rhs: HashMap::new(),
            last_len: (0, 0),
        }
    }
}

impl PredicateEncoder for IWoorpjeEncoder {
    fn encode(
        &mut self,
        bounds: &VariableBounds,
        substitution: &SubstitutionEncoding,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let lhs = &FilledPattern::fill(self.equation.lhs(), bounds);
        let rhs = &FilledPattern::fill(self.equation.rhs(), bounds);

        // TODO: Check if (lhs.len, rhs.len) == last_len and return assumptions from last call

        res.join(self.update_state_vars(lhs.length(), rhs.length()));
        res.join(self.update_pattern(lhs, rhs, substitution));
        res.join(self.align_patter(lhs, rhs, substitution));
        res.join(self.encode_successors());
        res.join(self.encode_predecessors());
        res.join(self.encode_transitions(substitution));
        res.join(self.encode_initial_state());
        res.join(self.encode_accepting_state());
        self.last_len = (lhs.length(), rhs.length());
        res
    }

    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        self.state_vars = Vec::new();
        self.last_len = (0, 0);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use cadical::Solver;

    use crate::{
        encode::substitution::SubstitutionEncoder,
        model::{words::Pattern, Sort, Variable},
    };

    fn solve_iwoorpje(
        eq: &WordEquation,
        bounds: VariableBounds,
        alphabet: &HashSet<char>,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), eq.variables());

        let subs_cnf = subs_encoder.encode(&bounds);
        encoding.join(subs_cnf);
        let mut encoder = IWoorpjeEncoder::new(eq.clone());
        encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding().unwrap()));

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
            let solution = subs_encoder
                .get_encoding()
                .unwrap()
                .get_substitutions(&solver);

            let svs = encoder.get_state_vars();

            for j in 0..svs[0].len() {
                print!("\t{}", j)
            }

            for i in 0..svs.len() {
                print!("{}\t", i);
                for j in 0..svs[i].len() {
                    if solver.value(as_lit(svs[i][j])) == Some(true) {
                        print!("1\t")
                    } else {
                        print!("0\t")
                    }
                }
            }
            assert!(
                eq.is_solution(&solution),
                "{:?} is not a solution: {:?} != {:?}",
                solution,
                eq.lhs().substitute(&solution),
                eq.rhs().substitute(&solution)
            );
        }
        res
    }

    fn solve_iwoorpje_incremental(
        eq: &WordEquation,
        limit: usize,
        alphabet: &HashSet<char>,
    ) -> Option<bool> {
        let mut bounds = VariableBounds::new(1);

        let mut encoder = IWoorpjeEncoder::new(eq.clone());
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), eq.variables());

        let mut result = None;
        let mut done = bounds.leq(limit);
        let mut solver: cadical::Solver = cadical::Solver::new();
        while done {
            println!("Next Round");
            let mut encoding = EncodingResult::empty();

            encoding.join(subs_encoder.encode(&bounds));
            encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding().unwrap()));
            result = match encoding {
                EncodingResult::Cnf(cnf, assm) => {
                    for clause in cnf {
                        solver.add_clause(clause);
                    }
                    solver.solve_with(assm.into_iter())
                }
                EncodingResult::Trivial(f) => Some(f),
            };
            done = bounds.next_square(Some(limit));
        }
        match result {
            Some(true) => {
                let sol = subs_encoder
                    .get_encoding()
                    .unwrap()
                    .get_substitutions(&solver);
                let svs = encoder.get_state_vars();
                for j in 0..svs[0].len() {
                    print!("\t{}", j)
                }
                println!();
                for i in 0..svs.len() {
                    print!("{}\t", i);
                    for j in 0..svs[i].len() {
                        if solver.value(as_lit(svs[i][j])) == Some(true) {
                            print!("1\t")
                        } else {
                            print!("0\t")
                        }
                    }
                    println!();
                }

                assert!(eq.is_solution(&sol), "Not a solution: {:?} ({})", sol, eq);
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
        let bounds = VariableBounds::new(10);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_sat_consts() {
        let eq = WordEquation::constant("bar", "bar");
        let bounds = VariableBounds::new(10);

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_unsat_consts() {
        let eq = WordEquation::constant("bar", "barr");
        let bounds = VariableBounds::new(10);

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn iwoorpje_trivial_sat_const_var() {
        let eq = WordEquation::new(
            Pattern::variable(&Variable::tmp_var(Sort::String)),
            Pattern::constant("bar"),
        );

        let bounds = VariableBounds::new(5);

        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_sat_vars() {
        let var = Pattern::variable(&Variable::tmp_var(Sort::String));
        let eq = WordEquation::new(var.clone(), var);
        let bounds = VariableBounds::new(10);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_sat_commute() {
        // AB = BA
        let var_a = Variable::tmp_var(Sort::String);
        let var_b = Variable::tmp_var(Sort::String);
        let mut lhs = Pattern::empty();
        lhs.append_var(&var_a).append_var(&var_b);
        let mut rhs = Pattern::empty();
        rhs.append_var(&var_b).append_var(&var_a);
        let eq = WordEquation::new(lhs, rhs);
        let bounds = VariableBounds::new(10);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_sat_pattern_const() {
        let var_a = Variable::tmp_var(Sort::String);

        let mut lhs = Pattern::empty();
        lhs.append_word("a").append_var(&var_a).append_word("c");
        let rhs = Pattern::constant("abc");
        let eq = WordEquation::new(lhs, rhs);
        let bounds = VariableBounds::new(3);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_test() {
        let eq = WordEquation::parse_simple("aXb", "YXb");
        let bounds = VariableBounds::new(3);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn iwoorpje_trivial_unsat_const_var_too_small() {
        let eq = WordEquation::new(
            Pattern::constant("foo"),
            Pattern::variable(&Variable::tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(1);

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
