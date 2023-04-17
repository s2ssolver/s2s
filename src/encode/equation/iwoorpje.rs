use std::collections::{HashMap, HashSet};

use crate::encode::card::exactly_one;
use crate::encode::substitution::SubstitutionEncoding;
use crate::encode::{
    EncodingResult, FilledPattern, FilledPos, PredicateEncoder, VariableBounds, LAMBDA,
};
use crate::model::words::WordEquation;
use crate::sat::{as_lit, neg, pvar, Clause, Cnf, PVar};

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
        bounds: &VariableBounds,
        lhs: &FilledPattern,
        rhs: &FilledPattern,
        subs: &SubstitutionEncoding,
    ) -> EncodingResult {
        let mut cnf = Cnf::new();
        assert!(self.pat_lhs.len() <= lhs.length(), "Pattern is shrinking");
        assert!(self.pat_rhs.len() <= rhs.length(), "Pattern is shrinking");

        // Left-hand side
        for i in self.pat_lhs.len()..lhs.length() {
            let mut choices = Vec::new();
            for c in subs.alphabet_lambda() {
                let v = pvar();
                choices.push(v);
                self.pat_lhs.insert((i, c), v);
            }
            cnf.extend(exactly_one(&choices));
        }
        // Right-hand side
        for i in self.pat_rhs.len()..rhs.length() {
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
                        // selector -> (sub_p <-> sub_x)
                        cnf.push(vec![-selector, -sub_p, sub_x]);
                        cnf.push(vec![-selector, sub_p, -sub_x]);
                    }
                }
            }
        }
        EncodingResult::Cnf(cnf, assms)
    }

    fn update_state_vars(&mut self, u_size: usize, v_size: usize) {
        let n_old = self.state_vars.len();

        for i in 0..u_size + 1 {
            if i < n_old {
                // Extend existing row
                for j in self.state_vars[i].len()..v_size + 1 {
                    self.state_vars[i].push(pvar());
                }
            } else {
                // Add new row
                let mut row = Vec::new();
                for j in 0..v_size + 1 {
                    row.push(pvar());
                }
                self.state_vars.push(row);
            }
        }

        assert_eq!(u_size + 1, self.state_vars.len());
        assert_eq!(v_size + 1, self.state_vars[0].len());
    }

    fn encode_successors(&mut self) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (n, m) = self.last_len;
        for i in n..self.state_vars.len() - 1 {
            for j in m..self.state_vars[i].len() - 1 {
                let s_00 = as_lit(self.state_vars[i][j]);
                let s_01 = as_lit(self.state_vars[i][j + 1]);
                let s_10 = as_lit(self.state_vars[i + 1][j]);
                let s_11 = as_lit(self.state_vars[i + 1][j + 1]);
                cnf.push(vec![-s_00, s_01, s_10, s_11]);
            }
        }
        for i in n..self.state_vars.len() - 1 {
            let s_00 = as_lit(self.state_vars[i][self.state_vars[i].len() - 1]);
            let s_10 = as_lit(self.state_vars[i + 1][self.state_vars[i].len() - 1]);
            cnf.push(vec![-s_00, s_10]);
        }
        for j in m..self.state_vars[self.state_vars.len() - 1].len() - 1 {
            let s_00 = as_lit(self.state_vars[self.state_vars.len() - 1][j]);
            let s_01 = as_lit(self.state_vars[self.state_vars.len() - 1][j + 1]);
            cnf.push(vec![-s_00, s_01]);
        }
        EncodingResult::cnf(cnf)
    }

    fn encode_predecessors(&mut self) -> EncodingResult {
        let mut cnf = Cnf::new();
        let (mut n, mut m) = self.last_len;
        n = std::cmp::max(n, 1);
        m = std::cmp::max(m, 1);
        for i in n..self.state_vars.len() {
            for j in m..self.state_vars[i].len() {
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
        let (n, m) = self.last_len;

        for i in n..self.state_vars.len() - 1 {
            for j in m..self.state_vars[i].len() - 1 {
                let s_00 = as_lit(self.state_vars[i][j]);
                let s_01 = as_lit(self.state_vars[i][j + 1]);
                let s_10 = as_lit(self.state_vars[i + 1][j]);
                let s_11 = as_lit(self.state_vars[i + 1][j + 1]);
                cnf.push(vec![-s_00, -s_10, as_lit(self.pat_lhs[&(i, LAMBDA)])]);
                cnf.push(vec![-s_00, -s_01, as_lit(self.pat_rhs[&(j, LAMBDA)])]);
                for c in subs.alphabet() {
                    let sub_l = self.pat_lhs[&(i, *c)];
                    let sub_r = self.pat_rhs[&(j, *c)];
                    cnf.push(vec![-s_00, -s_11, neg(sub_l), as_lit(sub_r)])
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
        let n = self.state_vars.len() - 1;
        let m = self.state_vars[n].len() - 1;
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
        let mut res = EncodingResult::Trivial(true);
        let lhs = &FilledPattern::fill(self.equation.lhs(), bounds);
        let rhs = &FilledPattern::fill(self.equation.rhs(), bounds);

        // TODO: Check if (lhs.len, rhs.len) == last_len and return assumptions from last call

        self.update_state_vars(lhs.length(), rhs.length());
        res.join(self.update_pattern(bounds, lhs, rhs, substitution));
        res.join(self.align_patter(lhs, rhs, substitution));
        res.join(self.encode_successors());
        res.join(self.encode_predecessors());
        res.join(self.encode_transitions(substitution));
        res.join(self.encode_initial_state());
        res.join(self.encode_accepting_state());
        // TODO: All positions that have no match on the other side are unconstrained, needs to be fixed
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
        println!("Solving {}", eq);
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
        println!("Assumptions: {:?}", assumptions);
        let res = solver.solve_with(assumptions.into_iter());
        if let Some(true) = res {
            let solution = subs_encoder
                .get_encoding()
                .unwrap()
                .get_substitutions(&solver);

            println!("Solution: {:?}", solution);
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
            Pattern::constant("bar"),
            Pattern::variable(&Variable::tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(19);

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
    fn iwoorpje_sat_t1i2() {
        // Track1, Instance 2
        //BabbabbadeeadAacbacaHaebHedbAcAcHebabccEcbcHH = AbbHabbAbbaHeFcadEbdeHbAcacdebabccAecbcdH
        let var_a = Variable::new("A".to_string(), Sort::String);
        let var_b = Variable::new("B".to_string(), Sort::String);
        let var_h = Variable::new("H".to_string(), Sort::String);
        let var_f = Variable::new("F".to_string(), Sort::String);
        let var_e = Variable::new("E".to_string(), Sort::String);

        // B abbabbadeead A acbaca H aeb H edb A c A c H ebabcc E cbc HH
        let mut lhs = Pattern::empty();
        lhs.append_var(&var_b)
            .append_word("abbabbadeead")
            .append_var(&var_a)
            .append_word("acbaca")
            .append_var(&var_h)
            .append_word("aeb")
            .append_var(&var_h)
            .append_word("edb")
            .append_var(&var_a)
            .append_word("c")
            .append_var(&var_a)
            .append_word("c")
            .append_var(&var_h)
            .append_word("ebabcc")
            .append_var(&var_e)
            .append_word("cbc")
            .append_var(&var_h)
            .append_var(&var_h);

        // A bb H abb A bba H e F cad E bde H b A cacdebabcc A ecbcd H
        let mut rhs = Pattern::empty();
        rhs.append_var(&var_a)
            .append_word("bb")
            .append_var(&var_h)
            .append_word("abb")
            .append_var(&var_a)
            .append_word("bba")
            .append_var(&var_h)
            .append_word("e")
            .append_var(&var_f)
            .append_word("cad")
            .append_var(&var_e)
            .append_word("bde")
            .append_var(&var_h)
            .append_word("b")
            .append_var(&var_a)
            .append_word("cacdebabcc")
            .append_var(&var_a)
            .append_word("ecbcd")
            .append_var(&var_h);

        assert_eq!(
            format!("{}", lhs),
            "BabbabbadeeadAacbacaHaebHedbAcAcHebabccEcbcHH"
        );
        assert_eq!(
            format!("{}", rhs),
            "AbbHabbAbbaHeFcadEbdeHbAcacdebabccAecbcdH"
        );

        let eq = WordEquation::new(lhs.clone(), rhs.clone());
        let solution = HashMap::from([
            (var_a, "a".to_string()),
            (var_b, "abbd".to_string()),
            (var_h, "d".to_string()),
            (var_f, "eadaacba".to_string()),
            (var_e, "ae".to_string()),
        ]);
        assert!(eq.is_solution(&solution));
        let bounds = VariableBounds::new(10);
        let res = solve_iwoorpje(&eq, bounds, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
}
