use std::cmp::min;

use rustsat::clause;

use super::matching::MatchEncoder;
use super::word::WordSetEncoding;

use crate::{
    domain::Domain,
    encode::{
        card::IncrementalALO, domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingResult,
        EncodingSink, LAMBDA,
    },
    ir::{Pattern, Symbol, WordEquation},
    sat::{nlit, pvar},
};

pub struct WordInEquationEncoder {
    lhs: Pattern,
    rhs: Pattern,
    match_lhs: MatchEncoder,
    match_rhs: MatchEncoder,
    word_encoding_lhs: Option<WordSetEncoding>,
    word_encoding_rhs: Option<WordSetEncoding>,
    mismatch_alo: IncrementalALO,
    lhs_bound: Option<usize>,
    rhs_bound: Option<usize>,
}

impl WordInEquationEncoder {
    pub fn new(eq: WordEquation) -> Self {
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        let match_lhs = MatchEncoder::new(lhs.clone());
        let match_rhs = MatchEncoder::new(rhs.clone());

        Self {
            lhs,
            rhs,
            match_lhs,
            match_rhs,
            word_encoding_lhs: None,
            word_encoding_rhs: None,
            mismatch_alo: IncrementalALO::new(),
            lhs_bound: None,
            rhs_bound: None,
        }
    }

    fn encode_solution_words(&mut self, l_lhs: usize, l_rhs: usize, sink: &mut impl EncodingSink) {
        self.word_encoding_lhs.as_mut().unwrap().encode(l_lhs, sink);
        self.word_encoding_rhs.as_mut().unwrap().encode(l_rhs, sink);
    }

    fn encode_matching(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) {
        self.match_lhs.encode(
            &self.word_encoding_lhs.as_ref().unwrap().into(),
            dom,
            dom_enc,
            sink,
        );

        self.match_rhs.encode(
            &self.word_encoding_rhs.as_ref().unwrap().into(),
            dom,
            dom_enc,
            sink,
        );
    }

    fn pattern_upper_bound(&self, pattern: &Pattern, dom: &Domain) -> usize {
        pattern
            .symbols()
            .map(|s| match s {
                Symbol::Constant(_) => 1,
                Symbol::Variable(v) => {
                    dom.get_string(v)
                        .and_then(|i| i.upper_finite())
                        .expect("Unbounded string variable") as usize
                }
            })
            .sum()
    }

    fn lhs_upper_bound(&self, dom: &Domain) -> usize {
        self.pattern_upper_bound(&self.lhs, dom)
    }

    fn rhs_upper_bound(&self, dom: &Domain) -> usize {
        self.pattern_upper_bound(&self.rhs, dom)
    }

    /// Encodes that the word the lhs is mapped differs from the word the rhs is mapped to.
    fn encode_mismatch(
        &mut self,
        dom: &DomainEncoding,
        l_lhs: usize,
        l_rhs: usize,
        sink: &mut impl EncodingSink,
    ) {
        let last_lhs_bound = self.lhs_bound.unwrap_or(0);
        let last_rhs_bound = self.rhs_bound.unwrap_or(0);

        // we need to compare up to the length of the smaller word and ensure that there is one position where they differ
        // Since the length of the word is one longer than the longest word a pattern can match, this also includes the case where one word is longer than the other (in that case, the last position of one word is lambda and the other is not)
        let last_bound = min(last_lhs_bound, last_rhs_bound);
        let next_bound = min(l_lhs, l_rhs);

        let wlhs = self.word_encoding_lhs.as_ref().unwrap();
        let wrhs = self.word_encoding_rhs.as_ref().unwrap();

        let mut new_mismatch_selectors = vec![];
        for pos in last_bound..next_bound {
            let v = pvar();
            new_mismatch_selectors.push(v);
            // If v is true, then there is a mismatch at position b
            for c in dom.alphabet().iter() {
                let lhs_c = wlhs.at(pos, c);
                let rhs_c = wrhs.at(pos, c);
                sink.add_clause(clause![nlit(v), nlit(lhs_c), nlit(rhs_c)]);
            }
            let lhs_lambda = wlhs.at(pos, LAMBDA);
            let rhs_lambda = wrhs.at(pos, LAMBDA);

            sink.add_clause(clause![nlit(v), nlit(lhs_lambda), nlit(rhs_lambda)]);
        }

        match self.mismatch_alo.add(&new_mismatch_selectors) {
            EncodingResult::Cnf(cnf, asm) => {
                sink.add_cnf(cnf);
                for i in asm {
                    sink.add_assumption(i);
                }
            }
            EncodingResult::Trivial(_) => todo!(),
        }
    }
}

impl EncodeLiteral for WordInEquationEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        if self.word_encoding_lhs.is_none() {
            self.word_encoding_lhs = Some(WordSetEncoding::new(dom_enc.alphabet().clone()));
        }
        if self.word_encoding_rhs.is_none() {
            self.word_encoding_rhs = Some(WordSetEncoding::new(dom_enc.alphabet().clone()));
        }

        // we allow both sides to map to any words in bounds
        // +1 is a technicality required by the encoding, see `encode_mismatch`
        let u_lhs = self.lhs_upper_bound(dom) + 1;
        let u_rhs = self.rhs_upper_bound(dom) + 1;
        self.encode_solution_words(u_lhs, u_rhs, sink);
        self.encode_matching(dom, dom_enc, sink);
        self.encode_mismatch(dom_enc, u_lhs, u_rhs, sink);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use itertools::Itertools;
    use rustsat_cadical::CaDiCaL;
    use smt_str::alphabet::CharRange;

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

    use super::WordInEquationEncoder;

    use rustsat::solvers::{Solve, SolveIncremental, SolverResult};

    fn solve_with_bounds(
        eq: &WordEquation,
        bounds: &[usize],
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        let mut alphabet: Alphabet = Alphabet::from_iter(eq.constants().iter().copied());
        alphabet.insert(CharRange::new('a', 'z'));
        let alphabet = Rc::new(alphabet);
        let mut domain = DomainEncoder::new(alphabet);

        let mut cadical: CaDiCaL = CaDiCaL::default();

        let mut encoder = WordInEquationEncoder::new(eq.clone());

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
                    print!("Solution WORD LHS: ");
                    encoder
                        .word_encoding_lhs
                        .as_ref()
                        .unwrap()
                        .print_solution_word(&cadical);
                    print!("Solution WORD RHS: ");
                    encoder
                        .word_encoding_rhs
                        .as_ref()
                        .unwrap()
                        .print_solution_word(&cadical);
                    println!("Start Positions LHS");
                    encoder.match_lhs.print_start_positions(&cadical);
                    println!("Start Positions RHS");
                    encoder.match_rhs.print_start_positions(&cadical);
                    println!("String lengths");
                    let solution = cadical.full_solution().unwrap();
                    for v in eq.variables() {
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
                Some(_) => continue,
                None => unreachable!(),
            }
        }
        None
    }

    fn assert_sat(eq: &WordEquation, bounds: &[usize], ctx: &mut Context) {
        match solve_with_bounds(eq, bounds, ctx) {
            Some(sol) => {
                assert!(
                    !is_solution(eq, &sol),
                    "Returned substitution\n\t{}\nis not a solution for\n\t!({})",
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
        assert_sat(&eq, &[1], &mut ctx);
        assert_sat(&eq, &[3], &mut ctx);
    }

    #[test]
    fn empty_eq() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("", "", &mut ctx);
        assert_unsat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn const_equality_sat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("foo", "foo", &mut ctx);
        assert_unsat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn const_equality_unsat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("foo", "bar", &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn const_equality_prefixes_unsat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("foo", "foofoo", &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn var_equality_trivial() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "X", &mut ctx);
        assert_unsat(&eq, &[0], &mut ctx);
        assert_unsat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn var_equality() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "Y", &mut ctx);
        assert_unsat(&eq, &[0], &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
    }

    #[test]
    fn var_equality_commute() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XY", "YX", &mut ctx);
        assert_unsat(&eq, &[0], &mut ctx);
        assert_sat(&eq, &[1, 2, 5, 10], &mut ctx);
    }

    #[test]
    fn concat_two_vars_const() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("XY", "abc", &mut ctx);
        assert_sat(&eq, &[0], &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
        assert_sat(&eq, &[1, 2, 3], &mut ctx);
    }

    #[test]
    fn simple_eq_1() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXc", "abc", &mut ctx);
        assert_sat(&eq, &[0], &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
        assert_sat(&eq, &[1, 2, 3], &mut ctx);
    }

    #[test]
    fn simple_eq_2() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXc", "abbbbc", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
        assert_sat(&eq, &[3], &mut ctx);
        assert_sat(&eq, &[2, 4], &mut ctx);
        assert_sat(&eq, &[4], &mut ctx);
    }

    #[test]
    fn simple_eq_3() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXb", "YXb", &mut ctx);
        assert_sat(&eq, &[1], &mut ctx);
    }
}
