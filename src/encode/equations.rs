use std::collections::HashMap;
use std::slice::Iter;

use super::{
    EncodingResult, PredicateEncoder, SubstitutionEncoding, VariableBounds, WordEquationEncoder,
    LAMBDA,
};
use crate::model::words::{Pattern, Symbol, WordEquation};
use crate::model::Variable;
use crate::sat::{as_lit, neg, pvar, Clause, Cnf, PVar};

/// A position in a filled pattern.
/// Either a constant word or a position within a variable.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FilledPos {
    Const(char),
    FilleVar(Variable, usize),
}
/// A filled pattern is a pattern with a set of bounds on the variables.
/// Each position in the pattern is either a constant word or a position within a variable.
struct FilledPattern {
    positions: Vec<FilledPos>,
}

impl FilledPattern {
    fn fill(pattern: &Pattern, bounds: &VariableBounds) -> Self {
        Self {
            positions: Self::convert(pattern, bounds),
        }
    }

    fn convert(pattern: &Pattern, bounds: &VariableBounds) -> Vec<FilledPos> {
        let mut positions = vec![];
        for symbol in pattern.symbols() {
            match symbol {
                Symbol::LiteralWord(s) => {
                    for c in s.chars() {
                        positions.push(FilledPos::Const(c))
                    }
                }
                Symbol::Variable(v) => {
                    let len = bounds.get(v);
                    for i in 0..len {
                        positions.push(FilledPos::FilleVar(v.clone(), i))
                    }
                }
            }
        }
        positions
    }

    pub fn length(&self) -> usize {
        self.positions.len()
    }

    fn at(&self, i: usize) -> Option<&FilledPos> {
        self.positions.get(i)
    }

    fn iter(&self) -> Iter<FilledPos> {
        self.positions.iter()
    }
}

pub struct WoorpjeEncoder {
    equation: WordEquation,
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
                            println!("({} == {}) <--> {}; {{{}}}", a, b, wm_var, wm_var);
                        } else {
                            println!("({} == {}) <--> {}; {{{}}} ", a, b, wm_var, neg(wm_var));
                            cnf.push(vec![neg(wm_var)])
                        }
                    }
                    (FilledPos::Const(a), FilledPos::FilleVar(v, vj)) => {
                        let sub_u = subs.get(&v, *vj, *a).unwrap();
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        cnf.push(vec![neg(wm_var), as_lit(sub_u)]);
                        cnf.push(vec![as_lit(wm_var), neg(sub_u)]);
                    }
                    (FilledPos::FilleVar(u, ui), FilledPos::Const(b)) => {
                        let sub_u = subs.get(&u, *ui, *b).unwrap();
                        let wm_var = pvar();
                        wm.insert((i, j), wm_var);
                        cnf.push(vec![neg(wm_var), as_lit(sub_u)]);
                        cnf.push(vec![as_lit(wm_var), neg(sub_u)]);
                    }
                    (FilledPos::FilleVar(u, ui), FilledPos::FilleVar(v, vj)) => {
                        for chr in subs.alphabet() {
                            let sub_u = subs.get(u, *ui, *chr).unwrap();
                            let sub_v = subs.get(v, *vj, *chr).unwrap();
                            let wm_var = pvar();
                            wm.insert((i, j), wm_var);
                            cnf.push(vec![neg(wm_var), as_lit(sub_u)]);
                            cnf.push(vec![neg(wm_var), as_lit(sub_v)]);
                            cnf.push(vec![neg(sub_v), neg(sub_u), as_lit(wm_var)]);
                        }
                    }
                }
            }
        }
        (wm, cnf)
    }
}

impl PredicateEncoder for WoorpjeEncoder {
    fn is_incremental(&self) -> bool {
        false
    }

    fn reset(&self) -> bool {
        todo!()
    }

    fn encode(&self, bounds: &VariableBounds, subs: &SubstitutionEncoding) -> EncodingResult {
        let mut cnf = Cnf::new();
        let lhs = FilledPattern::fill(&self.equation.lhs(), bounds);
        let rhs = FilledPattern::fill(&self.equation.rhs(), bounds);
        log::debug!("Encoding {}", self.equation);

        println!("{}", self.equation);
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

        for i in 0..n {
            for j in 0..m {
                let s_00 = as_lit(state_vars[i][j]);
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
                    FilledPos::Const(_) => {}
                    FilledPos::FilleVar(u, ui) => {
                        cnf.push(vec![-s_00, subs.get_lit(u, *ui, LAMBDA).unwrap(), s_10]);

                        match rhs.at(j).unwrap() {
                            FilledPos::Const(_) => {}
                            FilledPos::FilleVar(v, vj) => {
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
                    FilledPos::Const(_) => {}
                    FilledPos::FilleVar(v, vj) => {
                        cnf.push(vec![-s_00, subs.get_lit(v, *vj, LAMBDA).unwrap(), s_01]);

                        match lhs.at(i).unwrap() {
                            FilledPos::Const(_) => {}
                            FilledPos::FilleVar(u, ui) => {
                                cnf.push(vec![
                                    -s_00,
                                    -subs.get_lit(v, *vj, LAMBDA).unwrap(),
                                    subs.get_lit(u, *ui, LAMBDA).unwrap(),
                                    s_10,
                                ]);
                            }
                        }
                    }
                }

                // 7. Match two lambda transitions
                if let FilledPos::FilleVar(u, ui) = lhs.at(i).unwrap() {
                    if let FilledPos::FilleVar(v, vj) = rhs.at(j).unwrap() {
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

                // 10.
                cnf.push(vec![-s_11, s_00, s_10, s_01])
            }

            cnf.push(vec![as_lit(state_vars[0][0])]);
            cnf.push(vec![as_lit(state_vars[n][m])]);
        }

        EncodingResult::Cnf(cnf)
    }
}

impl WordEquationEncoder for WoorpjeEncoder {
    fn new(equation: WordEquation) -> Self {
        Self { equation: equation }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use cadical::Solver;

    use crate::{
        encode::substitution::SubstitutionEncoder,
        model::{Sort, Variable},
    };

    use super::*;

    #[test]
    fn length_literal_word() {
        let pattern = Pattern::from(vec![
            Symbol::LiteralWord(String::from("foo")),
            Symbol::LiteralWord(String::from("bar")),
        ]);
        let bounds = VariableBounds::new(5);
        assert_eq!(FilledPattern::fill(&pattern, &bounds).length(), 6);
    }

    #[test]
    fn length_variable() {
        let pattern = Pattern::from(vec![
            Symbol::LiteralWord(String::from("foo")),
            Symbol::Variable(Variable::new("X".to_string(), Sort::String)),
            Symbol::LiteralWord(String::from("bar")),
        ]);
        let mut bounds = VariableBounds::new(5);
        bounds.set(&Variable::new("X".to_string(), Sort::String), 3);
        assert_eq!(FilledPattern::fill(&pattern, &bounds).length(), 9);
    }

    fn solve_woorpje(
        eq: &WordEquation,
        bounds: VariableBounds,
        alphabet: &HashSet<char>,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), eq.variables());
        encoding.join(subs_encoder.encode(&bounds));

        let encoder = WoorpjeEncoder::new(eq.clone());
        encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding()));

        let mut solver: Solver = Solver::default();
        match encoding {
            EncodingResult::Cnf(cnf) => {
                for clause in cnf {
                    solver.add_clause(clause);
                }
            }
            EncodingResult::Trivial(false) => return Some(false),
            EncodingResult::Trivial(true) => return Some(true),
        }

        solver.solve()
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
        let eq = WordEquation::new(
            Pattern::from(vec![Symbol::LiteralWord(String::from("bar"))]),
            Pattern::from(vec![Symbol::LiteralWord(String::from("bar"))]),
        );
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_unsat_consts() {
        let eq = WordEquation::new(
            Pattern::from(vec![Symbol::LiteralWord(String::from("a"))]),
            Pattern::from(vec![Symbol::LiteralWord(String::from("b"))]),
        );
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn woorpje_trivial_sat_const_var() {
        let eq = WordEquation::new(
            Pattern::from(vec![Symbol::LiteralWord(String::from("foo"))]),
            Pattern::from(vec![Symbol::LiteralWord(String::from("X"))]),
        );
        let alphabet = HashSet::from_iter(vec!['f', 'o']);
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &alphabet);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_sat_vars() {
        let var = Pattern::from(vec![Symbol::Variable(Variable::tmp_var(Sort::String))]);
        let eq = WordEquation::new(var.clone(), var);
        let bounds = VariableBounds::new(10);

        let res = solve_woorpje(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn woorpje_trivial_unsat_const_var_too_small() {
        let eq = WordEquation::new(
            Pattern::from(vec![Symbol::LiteralWord(String::from("foo"))]),
            Pattern::from(vec![Symbol::LiteralWord(String::from("X"))]),
        );
        let alphabet = HashSet::from_iter(vec!['f', 'o']);

        let bounds = VariableBounds::new(1);

        let res = solve_woorpje(&eq, bounds, &alphabet);
        assert!(matches!(res, Some(false)));
    }
}
