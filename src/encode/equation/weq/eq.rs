use std::cmp::min;

use rustsat::clause;

use super::matching::MatchEncoder;
use super::word::WordSetEncoding;

use crate::{
    domain::Domain,
    encode::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink},
    ir::{Pattern, Symbol, WordEquation},
};

pub struct WordEquationEncoder {
    lhs: Pattern,
    rhs: Pattern,
    match_encoder: (MatchEncoder, MatchEncoder),
    word_encoding: Option<WordSetEncoding>,
}

impl WordEquationEncoder {
    pub fn new(eq: WordEquation) -> Self {
        let word_encoding = None;
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        let lhs_match = MatchEncoder::new(lhs.clone());
        let rhs_match = MatchEncoder::new(rhs.clone());
        let match_encoder = (lhs_match, rhs_match);
        Self {
            lhs,
            rhs,
            match_encoder,
            word_encoding,
        }
    }

    fn encode_solution_words(&mut self, length: usize, sink: &mut impl EncodingSink) {
        self.word_encoding.as_mut().unwrap().encode(length, sink)
    }

    fn encode_matching(
        &mut self,
        bounds: &Domain,
        dom: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) {
        match (self.lhs.as_constant(), self.rhs.as_constant()) {
            (None, None) => {
                self.match_encoder.0.encode(
                    &self.word_encoding.as_ref().unwrap().into(),
                    bounds,
                    dom,
                    sink,
                );
                self.match_encoder.1.encode(
                    &self.word_encoding.as_ref().unwrap().into(),
                    bounds,
                    dom,
                    sink,
                );
            }
            (None, Some(s)) => {
                self.match_encoder.0.encode(&s.into(), bounds, dom, sink);
            }
            (Some(s), None) => {
                self.match_encoder.1.encode(&s.into(), bounds, dom, sink);
            }
            (Some(s1), Some(s2)) => {
                if s1 != s2 {
                    // add the empty clause
                    sink.add_clause(clause!());
                }
            }
        }
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

impl EncodeLiteral for WordEquationEncoder {
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
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        if self.word_encoding.is_none() {
            self.word_encoding = Some(WordSetEncoding::new(dom.alphabet().clone()));
        }

        // The largest possible length of a solution word is the minumum of the largest word either side can be mapped to.
        // Adding +1 is a technicality to ensure that that empty variables can start 'after' the pattern ends.
        // Eg. in YX = a, a bound of 1 is sufficient but then X (which is empty) cannot start at position 1 and the encoding is unsatisfiable.
        // Thus we need to allow X to start after the last position, which we get by adding +1.
        let u = min(self.lhs_upper_bound(bounds), self.rhs_upper_bound(bounds)) + 1;

        self.encode_solution_words(u, sink);

        self.encode_matching(bounds, dom, sink);

        Ok(())
    }

    fn print_debug(&self, solver: &rustsat_cadical::CaDiCaL) {
        print!("Solution WORD: ");
        if let Some(enc) = self.word_encoding.as_ref() {
            enc.print_solution_word(solver);
        } else {
            println!("No solution word encoding");
        }

        println!("Start Positions LHS");
        self.match_encoder.0.print_start_positions(solver);
        println!("Start Positions RHS");
        self.match_encoder.1.print_start_positions(solver);
        println!("String lengths");
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use itertools::Itertools;
    use rustsat_cadical::CaDiCaL;

    use crate::{
        alphabet::Alphabet,
        ast::VarSubstitution,
        context::Context,
        domain::Domain,
        encode::{
            domain::DomainEncoder,
            equation::weq::testutils::{is_solution, parse_simple_equation},
            EncodeLiteral, ResultSink,
        },
        interval::Interval,
        ir::WordEquation,
        sat::plit,
    };
    use rustsat::solvers::{Solve, SolveIncremental, SolverResult};

    use super::WordEquationEncoder;

    fn solve_with_bounds(
        eq: &WordEquation,
        bounds: &[usize],
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
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

            let mut sink = ResultSink::default();
            domain.encode(&bounds, &mut sink);

            encoder
                .encode(&bounds, domain.encoding(), &mut sink)
                .unwrap();

            let res = sink.result();

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
                        .print_solution_word(&cadical);
                    println!("Start Positions LHS");
                    encoder.match_encoder.0.print_start_positions(&cadical);
                    println!("Start Positions RHS");
                    encoder.match_encoder.1.print_start_positions(&cadical);
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
                    let subs = domain.encoding().get_model(&cadical, ctx);
                    return Some(subs);
                }
                Some(SolverResult::Unsat) => continue,
                _ => unreachable!(),
            }
        }
        None
    }

    fn assert_sat(eq: &WordEquation, bounds: &[usize], ctx: &mut Context) {
        match solve_with_bounds(eq, bounds, ctx) {
            Some(sol) => {
                assert!(
                    is_solution(eq, &sol),
                    "Returned substitution\n\t{}\nis not a solution for\n\t{}",
                    sol,
                    eq
                );
            }
            None => panic!("Expected SAT"),
        }
    }

    fn assert_unsat(eq: &WordEquation, bounds: &[usize], ctx: &mut Context) {
        if let Some(sol) = solve_with_bounds(eq, bounds, ctx) {
            panic!("Expected UNSAT, got solution: {}", sol);
        }
    }

    #[test]
    fn const_assignment() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "abc", &mut ctx);
        assert_unsat(&eq, &[1], &mut ctx);
        assert_unsat(&eq, &[2], &mut ctx);
        assert_sat(&eq, &[3], &mut ctx);
        assert_sat(&eq, &[1, 2, 3], &mut ctx);
    }

    #[test]
    fn empty_eq() {
        let mut ctx = Context::default();
        ctx.ast().set_simplify(false);
        let eq = parse_simple_equation("", "", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx)
    }

    #[test]
    fn const_equality_sat() {
        let mut ctx = Context::default();
        ctx.ast().set_simplify(false);
        let eq = parse_simple_equation("foo", "foo", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn const_equality_unsat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("foo", "bar", &mut ctx);
        assert_unsat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn const_equality_prefixes_unsat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("foo", "foofoo", &mut ctx);
        assert_unsat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn var_equality_trivial() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "X", &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn var_equality() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "Y", &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn var_equality_commute() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XY", "YX", &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn concat_two_vars_const() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XY", "abc", &mut ctx);
        assert_unsat(&eq, &[1], &mut ctx);
        assert_sat(&eq, &[2], &mut ctx);
        //assert_sat(&eq, &[1, 2, 3]);
    }

    #[test]
    fn simple_eq_1() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXc", "abc", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn simple_eq_2() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXc", "abbbbc", &mut ctx);
        assert_unsat(&eq, &[1], &mut ctx);
        assert_unsat(&eq, &[3], &mut ctx);
        assert_sat(&eq, &[2, 4], &mut ctx);
        assert_sat(&eq, &[4], &mut ctx);
    }

    #[test]
    fn simple_eq_3() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXb", "YXb", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn simple_eq_4() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXb", "YXc", &mut ctx);
        assert_unsat(&eq, &[1, 2, 5, 10, 20], &mut ctx);
    }

    #[test]
    fn woorpje_track1_eq17() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation(
            "A",
            "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd",
            &mut ctx,
        );
        assert_unsat(&eq, &[1, 2, 5, 10, 20], &mut ctx);
        assert_sat(&eq, &[20, 50], &mut ctx);
    }

    #[test]
    fn woorpje_track1_eq11() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation(
            "cfcbbAadeeaecAgebegeecafegebdbagddaadbddcaeeebfabfefabfacdgAgaabg",
            "AfcbbAaIegeeAaD",
            &mut ctx,
        );
        assert_unsat(&eq, &[1, 2, 5, 10, 20], &mut ctx);
        assert_sat(&eq, &[20, 50], &mut ctx);
    }

    #[test]
    fn woorpje_track1_eq97() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("AccAbccB", "CccAbDbcCcA", &mut ctx);
        assert_unsat(&eq, &[1, 2], &mut ctx);
        assert_sat(&eq, &[3], &mut ctx);
        assert_sat(&eq, &[1, 2, 3], &mut ctx);
    }
}
