//! Contains the original Woorpje encoding for word equations introduced in
//!
//! > Day, J.D., Ehlers, T., Kulczynski, M., Manea, F., Nowotka, D., Poulsen, D.B. (2019).
//! > On Solving Word Equations Using SAT. In: Filiot, E., Jungers, R., Potapov, I. (eds) Reachability Problems. RP 2019.
//! > Lecture Notes in Computer Science(), vol 11674. Springer, Cham. https://doi.org/10.1007/978-3-030-30806-3_8
//!
//! This is a non-complete re-implementation of the original version, which can be found in the [Woorpje repository](https://git.zs.informatik.uni-kiel.de/dbp/wordsolve).
//! Encoding of linear arithmetic over the length abstraction is not included in this implementation.
//!
//! The following changes have been made:
//! - Constraint (9) is no used, as it seems to be redundant. The original implementation does not use it either.
//! - Only one implication of $wm_{i,j}$ variables is encoded: $wm_{i,j} \rigtharrow ...$, but not $... \rigtharrow wm_{i,j}$. Again, this aligns with the original implementation. Satisfiability is not affected with this change.
//! - The fixes a bug where some unsat equations were incorrectly reported as sat due the original encoding did not correctly constraint the state variables in some corner cases.
use std::collections::HashMap;

use crate::encode::substitution::SubstitutionEncoding;
use crate::encode::{
    EncodingResult, FilledPattern, FilledPos, PredicateEncoder, VariableBounds, LAMBDA,
};
use crate::model::words::WordEquation;
use crate::sat::{as_lit, neg, pvar, Clause, Cnf, PVar};

use super::WordEquationEncoder;

pub struct WoorpjeEncoder {
    equation: WordEquation,
    state_vars: Option<Vec<Vec<PVar>>>,
}

impl WoorpjeEncoder {
    fn match_vars(
        &self,
        lhs: &FilledPattern,
        rhs: &FilledPattern,
        subs: &SubstitutionEncoding,
    ) -> (HashMap<(usize, usize), PVar>, Vec<Clause>) {
        let mut wm = HashMap::new();
        let mut cnf = Cnf::new();
        for i in 0..lhs.length() {
            for j in 0..rhs.length() {
                let pos_lhs = lhs.at(i).unwrap();
                let pos_rhs = rhs.at(j).unwrap();
                match (pos_lhs, pos_rhs) {
                    (FilledPos::Const(a), FilledPos::Const(b)) => {
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        if a == b {
                            cnf.push(vec![as_lit(wm_var)]);
                        } else {
                            cnf.push(vec![neg(wm_var)])
                        }
                    }
                    (FilledPos::Const(a), FilledPos::FilledPos(v, vj)) => {
                        let sub_u = subs.get(v, *vj, *a).unwrap();
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        cnf.push(vec![neg(wm_var), as_lit(sub_u)]);
                        cnf.push(vec![as_lit(wm_var), neg(sub_u)]);
                    }
                    (FilledPos::FilledPos(u, ui), FilledPos::Const(b)) => {
                        let sub_u = subs.get(u, *ui, *b).unwrap();
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        cnf.push(vec![neg(wm_var), as_lit(sub_u)]);
                        cnf.push(vec![as_lit(wm_var), neg(sub_u)]);
                    }
                    (FilledPos::FilledPos(u, ui), FilledPos::FilledPos(v, vj)) => {
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        // Clause for /\... -> wm_var
                        // let mut clause = vec![as_lit(wm_var)];
                        for chr in subs.alphabet_lambda() {
                            let sub_u = subs.get(u, *ui, chr).unwrap();
                            let sub_v = subs.get(v, *vj, chr).unwrap();

                            // wm_var => sub_u /\ sub_v
                            cnf.push(vec![neg(wm_var), neg(sub_u), as_lit(sub_v)]);

                            // We don't (seem to) actually need the other direction as we don't do decisions based on wm_{i,j}.
                            // Tseitin encoding for ltr implication
                            /*let t = pvar();
                            clause.push(as_lit(t));
                            cnf.push(vec![neg(t), as_lit(sub_u)]);
                            cnf.push(vec![neg(t), as_lit(sub_v)]);
                            cnf.push(vec![neg(sub_u), neg(sub_v), as_lit(t)]);*/
                        }
                        //cnf.push(clause);
                    }
                }
            }
        }
        (wm, cnf)
    }

    #[allow(dead_code)]
    fn get_state_vars(&self) -> Option<&Vec<Vec<PVar>>> {
        self.state_vars.as_ref()
    }
}

impl PredicateEncoder for WoorpjeEncoder {
    fn is_incremental(&self) -> bool {
        false
    }

    fn reset(&mut self) { // do nothing}
    }

    fn encode(&mut self, bounds: &VariableBounds, subs: &SubstitutionEncoding) -> EncodingResult {
        let mut cnf = Cnf::new();
        let lhs = FilledPattern::fill(self.equation.lhs(), bounds);
        let rhs = FilledPattern::fill(self.equation.rhs(), bounds);
        log::debug!(
            "Encoding {} ({} x {})",
            self.equation,
            lhs.length(),
            rhs.length()
        );

        let (wm, wm_cnf) = self.match_vars(&lhs, &rhs, subs);
        cnf.extend(wm_cnf);
        let n = lhs.length();
        let m = rhs.length();
        if n == 0 {
            return EncodingResult::Trivial(!self.equation.rhs().contains_constant());
        }
        if m == 0 {
            return EncodingResult::Trivial(!self.equation.lhs().contains_constant());
        }

        // Initialize state variables
        let mut state_vars = vec![vec![0; m + 1]; n + 1];

        state_vars
            .iter_mut()
            .for_each(|v| v.iter_mut().for_each(|x| *x = pvar()));
        log::debug!("Created {} state variables", n * m);
        for i in 0..=n {
            for j in 0..=m {
                let s_00 = as_lit(state_vars[i][j]);

                if i < n && j < m {
                    let s_10 = as_lit(state_vars[i + 1][j]);
                    let s_01 = as_lit(state_vars[i][j + 1]);
                    let s_11 = as_lit(state_vars[i + 1][j + 1]);

                    // 1. At least one successor state
                    cnf.push(vec![-s_00, s_01, s_10, s_11]);

                    // 2. At most one successor state (a)
                    cnf.push(vec![-s_00, -s_01, -s_11]); // s_00 /\ s_01 --> -s_11
                    cnf.push(vec![-s_00, -s_01, -s_10]); // s_00 /\ s_01 --> -s_10

                    // 3. At most one successor state (b)
                    cnf.push(vec![-s_00, -s_10, -s_11]); // s_00 /\ s_10 --> -s_11
                    cnf.push(vec![-s_00, -s_10, -s_01]); // s_00 /\ s_10 --> -s_01

                    // 4. At most one successor state (c)
                    cnf.push(vec![-s_00, -s_11, -s_10]); // s_00 /\ s_11 --> -s_10
                    cnf.push(vec![-s_00, -s_11, -s_01]); // s_00 /\ s_11 --> -s_01

                    // 5. Substitution transition  (a)
                    match lhs.at(i).unwrap() {
                        FilledPos::Const(_) => {
                            cnf.push(vec![-s_00, -s_10]);
                        }
                        FilledPos::FilledPos(u, ui) => {
                            cnf.push(vec![-s_00, subs.get_lit(u, *ui, LAMBDA).unwrap(), -s_10]);

                            match rhs.at(j).unwrap() {
                                FilledPos::Const(_) => {
                                    cnf.push(vec![
                                        -s_00,
                                        -subs.get_lit(u, *ui, LAMBDA).unwrap(),
                                        s_10,
                                    ]);
                                }
                                FilledPos::FilledPos(v, vj) => {
                                    cnf.push(vec![
                                        -s_00,
                                        -subs.get_lit(u, *ui, LAMBDA).unwrap(),
                                        subs.get_lit(v, *vj, LAMBDA).unwrap(),
                                        s_10,
                                    ]);
                                }
                            }
                        }
                    }

                    // 6. Substitution transition (b)
                    match rhs.at(j).unwrap() {
                        FilledPos::Const(_) => {
                            cnf.push(vec![-s_00, -s_01]);
                        }
                        FilledPos::FilledPos(v, vj) => {
                            cnf.push(vec![-s_00, subs.get_lit(v, *vj, LAMBDA).unwrap(), -s_01]);

                            match lhs.at(i).unwrap() {
                                FilledPos::Const(_) => {
                                    cnf.push(vec![
                                        -s_00,
                                        -subs.get_lit(v, *vj, LAMBDA).unwrap(),
                                        s_01,
                                    ]);
                                }
                                FilledPos::FilledPos(u, ui) => {
                                    cnf.push(vec![
                                        -s_00,
                                        -subs.get_lit(v, *vj, LAMBDA).unwrap(),
                                        subs.get_lit(u, *ui, LAMBDA).unwrap(),
                                        s_01,
                                    ]);
                                }
                            }
                        }
                    }

                    // 7. Match two lambda transitions
                    if let FilledPos::FilledPos(u, ui) = lhs.at(i).unwrap() {
                        if let FilledPos::FilledPos(v, vj) = rhs.at(j).unwrap() {
                            cnf.push(vec![
                                -s_00,
                                -subs.get_lit(u, *ui, LAMBDA).unwrap(),
                                -subs.get_lit(v, *vj, LAMBDA).unwrap(),
                                s_11,
                            ]);
                        }
                    }

                    // 8. Matching letters at position i,j
                    cnf.push(vec![-s_00, -s_11, as_lit(*wm.get(&(i, j)).unwrap())]);

                    // 9. Possible transitions

                    // 10. Predecessor states
                    cnf.push(vec![-s_11, s_00, s_01, s_10]);
                } else if i < n && j == m {
                    let s_10 = as_lit(state_vars[i + 1][j]);

                    // 1. At least one successor state
                    cnf.push(vec![-s_00, s_10]);

                    // 5. Substitution transition  (a)
                    match lhs.at(i).unwrap() {
                        FilledPos::Const(_) => {
                            cnf.push(vec![-s_00, -s_10]);
                        }
                        FilledPos::FilledPos(u, ui) => {
                            cnf.push(vec![-s_00, subs.get_lit(u, *ui, LAMBDA).unwrap(), -s_10]);
                        }
                    }
                }
                if i == n && j < m {
                    let s_01 = as_lit(state_vars[i][j + 1]);

                    // 1. At least one successor state
                    cnf.push(vec![-s_00, s_01]);

                    // 6. Substitution transition (b)
                    match rhs.at(j).unwrap() {
                        FilledPos::Const(_) => {
                            cnf.push(vec![-s_00, -s_01]);
                        }
                        FilledPos::FilledPos(v, vj) => {
                            cnf.push(vec![-s_00, subs.get_lit(v, *vj, LAMBDA).unwrap(), -s_01]);
                        }
                    }
                }
            }
        }
        // TODO: move in loop above
        for j in 1..=m {
            cnf.push(vec![neg(state_vars[0][j]), as_lit(state_vars[0][j - 1])]);
        }
        for i in 1..=n {
            cnf.push(vec![neg(state_vars[i][0]), as_lit(state_vars[i - 1][0])]);
        }
        cnf.push(vec![as_lit(state_vars[0][0])]);
        cnf.push(vec![as_lit(state_vars[n][m])]);
        self.state_vars = Some(state_vars);
        EncodingResult::cnf(cnf)
    }
}

impl WordEquationEncoder for WoorpjeEncoder {
    fn new(equation: WordEquation) -> Self {
        Self {
            equation,
            state_vars: None,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use cadical::Solver;

    use indexmap::IndexSet;
    use quickcheck_macros::quickcheck;

    use crate::{
        encode::substitution::SubstitutionEncoder,
        formula::{ConstVal, Substitution},
        model::{words::Pattern, Sort, VarManager, Variable},
    };

    #[quickcheck]
    fn length_literal_word(word: String, bound: u8) {
        let bound = bound as usize;
        let pattern = Pattern::constant(&word);
        let bounds = VariableBounds::new(bound);
        assert_eq!(
            FilledPattern::fill(&pattern, &bounds).length(),
            word.chars().count()
        );
    }

    #[quickcheck]
    fn length_single_var_pattern(prefix: String, bound: u8, suffix: String) {
        let mut vm = VarManager::new();
        let bound = bound as usize;
        let v = vm.tmp_var(Sort::String);
        let mut pattern = Pattern::constant(&prefix);
        pattern.append_var(&v).append_word(&suffix);

        let mut bounds = VariableBounds::new(1);
        bounds.set(&v, bound);
        assert_eq!(
            FilledPattern::fill(&pattern, &bounds).length(),
            bound + prefix.chars().count() + suffix.chars().count()
        );
    }

    #[quickcheck]
    fn length_default_bound(prefix: String, default_bound: u8, suffix: String) {
        let mut vm = VarManager::new();
        let default_bound = default_bound as usize;
        let v = vm.tmp_var(Sort::String);
        let y = vm.tmp_var(Sort::String);
        let mut pattern = Pattern::constant(&prefix);
        pattern.append_var(&v).append_var(&y).append_word(&suffix);

        let mut bounds = VariableBounds::new(default_bound);
        bounds.set(&v, 1);
        assert_eq!(
            FilledPattern::fill(&pattern, &bounds).length(),
            1 + prefix.chars().count() + suffix.chars().count() + default_bound
        );
    }

    fn solve_woorpje(
        eq: &WordEquation,
        bounds: VariableBounds,
        alphabet: &IndexSet<char>,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();
        let mut vm = VarManager::new();
        eq.variables().iter().for_each(|v| {
            vm.new_var(v.name(), Sort::String);
        });
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), &vm);

        let subs_cnf = subs_encoder.encode(&bounds);
        encoding.join(subs_cnf);

        let mut encoder = WoorpjeEncoder::new(eq.clone());
        encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding().unwrap()));

        let mut solver: Solver = Solver::default();
        match encoding {
            EncodingResult::Cnf(cnf, _) => {
                for clause in cnf {
                    solver.add_clause(clause);
                }
            }
            EncodingResult::Trivial(false) => return Some(false),
            EncodingResult::Trivial(true) => return Some(true),
        }

        let res = solver.solve();
        if let Some(true) = res {
            let subs = subs_encoder
                .get_encoding()
                .unwrap()
                .get_substitutions(&solver);
            let mut solution = Substitution::with_defaults();
            for (v, val) in subs {
                solution.set(&v, ConstVal::String(val));
            }
            assert!(
                eq.is_solution(&solution).unwrap(),
                "{} is not a solution: {:?} != {:?}",
                solution,
                eq.lhs().substitute(&solution),
                eq.rhs().substitute(&solution)
            );
            println!("Solution: {}", solution);
            if let Some(svs) = encoder.get_state_vars() {
                for j in 0..svs[0].len() {
                    print!("\t{}", j)
                }
                println!();
                for (i, s) in svs.iter().enumerate() {
                    print!("{}\t", i);
                    for j in 0..s.len() {
                        if solver.value(as_lit(svs[i][j])) == Some(true) {
                            print!("1\t")
                        } else {
                            print!("0\t")
                        }
                    }
                }
            }
        }
        res
    }

    #[test]
    fn woorpje_empty_eq() {
        let eq = WordEquation::new(Pattern::from(vec![]), Pattern::from(vec![]));
        let bounds = VariableBounds::new(10);
        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_sat_consts() {
        let eq = WordEquation::constant("bar", "bar");
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_unsat_consts() {
        let eq = WordEquation::constant("bar", "barr");
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn woorpje_trivial_sat_const_var() {
        let mut vm = VarManager::new();
        let eq = WordEquation::new(
            Pattern::constant("bar"),
            Pattern::variable(&vm.tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(19);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_sat_vars() {
        let mut vm = VarManager::new();
        let var = Pattern::variable(&vm.tmp_var(Sort::String));
        let eq = WordEquation::new(var.clone(), var);
        let bounds = VariableBounds::new(10);
        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_sat_commute() {
        // AB = BA
        let mut vm = VarManager::new();
        let var_a = vm.tmp_var(Sort::String);
        let var_b = vm.tmp_var(Sort::String);
        let mut lhs = Pattern::empty();
        lhs.append_var(&var_a).append_var(&var_b);
        let mut rhs = Pattern::empty();
        rhs.append_var(&var_b).append_var(&var_a);
        let eq = WordEquation::new(lhs, rhs);
        let bounds = VariableBounds::new(10);
        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_sat_pattern_const() {
        let mut vm = VarManager::new();
        let var_a = vm.tmp_var(Sort::String);

        let mut lhs = Pattern::empty();
        lhs.append_word("a").append_var(&var_a).append_word("c");
        let rhs = Pattern::constant("abc");
        let eq = WordEquation::new(lhs, rhs);
        let bounds = VariableBounds::new(3);
        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_unsat_const_var_too_small() {
        let mut vm = VarManager::new();
        let eq = WordEquation::new(
            Pattern::constant("foo"),
            Pattern::variable(&vm.tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(1);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn woorpje_sat_t1i2() {
        // Track1, Instance 2
        //BabbabbadeeadAacbacaHaebHedbAcAcHebabccEcbcHH = AbbHabbAbbaHeFcadEbdeHbAcacdebabccAecbcdH
        let mut vm = VarManager::new();
        let var_a = vm.new_var("A", Sort::String);
        let var_b = vm.new_var("B", Sort::String);
        let var_h = vm.new_var("H", Sort::String);
        let var_f = vm.new_var("F", Sort::String);
        let var_e = vm.new_var("E", Sort::String);

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
        let solution: HashMap<Variable, Vec<char>> = HashMap::from([
            (var_a, "a".chars().collect()),
            (var_b, "abbd".chars().collect()),
            (var_h, "d".chars().collect()),
            (var_f, "eadaacba".chars().collect()),
            (var_e, "ae".chars().collect()),
        ]);
        let _solution = Substitution::from(solution);
        let bounds = VariableBounds::new(10);
        let res = solve_woorpje(&eq, bounds, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
}
