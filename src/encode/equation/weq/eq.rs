use std::cmp::min;

use super::matching::PatternMatchingEncoder;
use super::word::WordEncoding;

use crate::{
    domain::Domain,
    encode::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder},
    node::canonical::{Pattern, Symbol, WordEquation},
};

pub struct WordEquationEncoder {
    lhs: Pattern,
    rhs: Pattern,
    match_encoder: (PatternMatchingEncoder, PatternMatchingEncoder),
    word_encoding: Option<WordEncoding>,
}

impl WordEquationEncoder {
    pub fn new(eq: WordEquation) -> Self {
        let word_encoding = None;
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        let lhs_match = PatternMatchingEncoder::new(lhs.clone());
        let rhs_match = PatternMatchingEncoder::new(rhs.clone());
        let match_encoder = (lhs_match, rhs_match);
        Self {
            lhs,
            rhs,
            match_encoder,
            word_encoding,
        }
    }

    fn encode_solution_words(&mut self, length: usize) -> EncodingResult {
        self.word_encoding.as_mut().unwrap().encode(length)
    }

    fn encode_matching(&mut self, bounds: &Domain, dom: &DomainEncoding) -> EncodingResult {
        let mut res =
            self.match_encoder
                .0
                .encode(self.word_encoding.as_ref().unwrap(), bounds, dom);
        res.extend(
            self.match_encoder
                .1
                .encode(self.word_encoding.as_ref().unwrap(), bounds, dom),
        );
        res
    }

    fn pattern_upper_bound(&self, pattern: &Pattern, dom: &Domain) -> usize {
        pattern
            .symbols()
            .map(|s| match s {
                Symbol::Constant(_) => 1,
                Symbol::Variable(v) => {
                    dom.get_string(v)
                        .and_then(|i| i.upper_finite())
                        .expect("Upper bound not finite") as usize
                }
            })
            .sum()
    }

    fn lhs_upper_bound(&self, bounds: &Domain) -> usize {
        self.pattern_upper_bound(&self.lhs, bounds)
    }

    fn rhs_upper_bound(&self, bounds: &Domain) -> usize {
        self.pattern_upper_bound(&self.rhs, bounds)
    }
}

impl LiteralEncoder for WordEquationEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Domain,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.word_encoding.is_none() {
            self.word_encoding = Some(WordEncoding::new(dom.alphabet().clone()));
        }

        // The largest possible length of a solution word is the minumum of the largest word either side can be mapped to.
        // Adding +1 is a technicality to ensure that that empty variables can start 'after' the pattern ends.
        // Eg. in YX = a, a bound of 1 is sufficient but then X (which is empty) cannot start at position 1 and the encoding is unsatisfiable.
        // Thus we need to allow X to start after the last position, which we get by adding +1.
        let u = min(self.lhs_upper_bound(bounds), self.rhs_upper_bound(bounds)) + 1;

        let mut res = self.encode_solution_words(u);

        res.extend(self.encode_matching(bounds, dom));

        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use itertools::Itertools;
    use rustsat_cadical::CaDiCaL;

    use crate::{
        alphabet::Alphabet,
        domain::Domain,
        encode::{
            domain::DomainEncoder, equation::weq::testutils::parse_simple_equation, LiteralEncoder,
        },
        interval::Interval,
        node::{
            canonical::{Assignment, WordEquation},
            NodeManager,
        },
        sat::plit,
    };
    use rustsat::solvers::{Solve, SolveIncremental, SolverResult};

    use super::WordEquationEncoder;

    fn solve_with_bounds(eq: &WordEquation, bounds: &[usize]) -> Option<Assignment> {
        let alphabet: Alphabet = Alphabet::from_iter(eq.constants().iter().copied());
        let alphabet = Rc::new(alphabet);
        let mut domain = DomainEncoder::new(alphabet);

        let mut cadical = CaDiCaL::default();

        let mut encoder = WordEquationEncoder::new(eq.clone());

        for b in bounds {
            let mut bounds = Domain::empty();
            for v in eq.variables() {
                bounds.set_string(v, Interval::bounded_above(*b));
            }

            let mut res = domain.encode(&bounds);

            res.extend(encoder.encode(&bounds, domain.encoding()).unwrap());

            let assm = res.assumptions();

            cadical.add_cnf(res.into_inner().0).unwrap();
            let assm = assm.into_iter().collect_vec();
            match cadical.solve_assumps(&assm).ok() {
                Some(SolverResult::Sat) => {
                    print!("Solution WORD: ");
                    encoder
                        .word_encoding
                        .as_ref()
                        .unwrap()
                        .print_solution_word(&mut cadical);
                    println!("Start Positions LHS");
                    encoder.match_encoder.0.print_start_positions(&mut cadical);
                    println!("Start Positions RHS");
                    encoder.match_encoder.1.print_start_positions(&mut cadical);
                    println!("String lengths");
                    for v in eq.variables() {
                        let solution = cadical.full_solution().unwrap();
                        let mut found = false;
                        for l in 0..=*b {
                            let var = domain.encoding().string().get_len(&v, l).unwrap();
                            if solution.lit_value(plit(var)).to_bool_with_def(false) {
                                println!("\t|{}| = {}", v, l);
                                found = true;
                            }
                        }
                        assert!(found);
                    }
                    let subs = domain.encoding().get_model(&mut cadical);
                    return Some(subs);
                }
                Some(SolverResult::Unsat) => continue,
                _ => unreachable!(),
            }
        }
        None
    }

    fn assert_sat(eq: &WordEquation, bounds: &[usize]) {
        match solve_with_bounds(eq, bounds) {
            Some(sol) => {
                assert!(
                    sol.satisfies_word_equation(eq).unwrap(),
                    "Returned substitution\n\t{}\nis not a solution for\n\t{}",
                    sol,
                    eq
                );
            }
            None => panic!("Expected SAT"),
        }
    }

    fn assert_unsat(eq: &WordEquation, bounds: &[usize]) {
        if let Some(sol) = solve_with_bounds(eq, bounds) {
            panic!("Expected UNSAT, got solution: {}", sol);
        }
    }

    #[test]
    fn const_assignment() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("X", "abc", &mut mngr);
        assert_unsat(&eq, &[1]);
        assert_unsat(&eq, &[2]);
        assert_sat(&eq, &[3]);
        assert_sat(&eq, &[1, 2, 3]);
    }

    #[test]
    fn empty_eq() {
        let mut mngr = NodeManager::default();
        mngr.set_optimize(false);
        let eq = parse_simple_equation("", "", &mut mngr);
        assert_sat(&eq, &[1])
    }

    #[test]
    fn const_equality_sat() {
        let mut mngr = NodeManager::default();
        mngr.set_optimize(false);
        let eq = parse_simple_equation("foo", "foo", &mut mngr);
        assert_sat(&eq, &[1]);
    }

    #[test]
    fn const_equality_unsat() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("foo", "bar", &mut mngr);
        assert_unsat(&eq, &[1, 2, 5, 10]);
    }

    #[test]
    fn const_equality_prefixes_unsat() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("foo", "foofoo", &mut mngr);
        assert_unsat(&eq, &[1, 2, 5, 10]);
    }

    #[test]
    fn var_equality_trivial() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("X", "X", &mut mngr);
        assert_sat(&eq, &[1, 2, 5, 10]);
    }

    #[test]
    fn var_equality() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("X", "Y", &mut mngr);
        assert_sat(&eq, &[1, 2, 5, 10]);
    }

    #[test]
    fn var_equality_commute() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("XY", "YX", &mut mngr);
        assert_sat(&eq, &[1, 2, 5, 10]);
    }

    #[test]
    fn concat_two_vars_const() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("XY", "abc", &mut mngr);
        assert_unsat(&eq, &[1]);
        assert_sat(&eq, &[2]);
        assert_sat(&eq, &[1, 2, 3]);
    }

    #[test]
    fn simple_eq_1() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("aXc", "abc", &mut mngr);
        assert_sat(&eq, &[1]);
    }

    #[test]
    fn simple_eq_2() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("aXc", "abbbbc", &mut mngr);
        assert_unsat(&eq, &[1]);
        assert_unsat(&eq, &[3]);
        assert_sat(&eq, &[2, 4]);
        assert_sat(&eq, &[4]);
    }

    #[test]
    fn simple_eq_3() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("aXb", "YXb", &mut mngr);
        assert_sat(&eq, &[1]);
    }

    #[test]
    fn simple_eq_4() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("aXb", "YXc", &mut mngr);
        assert_unsat(&eq, &[1, 2, 5, 10, 20]);
    }

    #[test]
    fn woorpje_track1_eq17() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation(
            "A",
            "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd",
            &mut mngr,
        );
        assert_unsat(&eq, &[1, 2, 5, 10, 20]);
        assert_sat(&eq, &[20, 50]);
    }

    #[test]
    fn woorpje_track1_eq11() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation(
            "cfcbbAadeeaecAgebegeecafegebdbagddaadbddcaeeebfabfefabfacdgAgaabg",
            "AfcbbAaIegeeAaD",
            &mut mngr,
        );
        assert_unsat(&eq, &[1, 2, 5, 10, 20]);
        assert_sat(&eq, &[20, 50]);
    }

    #[test]
    fn woorpje_track1_eq97() {
        let mut mngr = NodeManager::default();
        let eq = parse_simple_equation("AccAbccB", "CccAbDbcCcA", &mut mngr);
        assert_unsat(&eq, &[1, 2]);
        assert_sat(&eq, &[3]);
        assert_sat(&eq, &[1, 2, 3]);
    }
}
