use std::cmp::min;

use super::matching::PatternMatchingEncoder;
use super::word::WordEncoding;

use crate::{
    bounds::Bounds,
    encode::{
        card::IncrementalALO, domain::DomainEncoding, EncodingError, EncodingResult,
        LiteralEncoder, LAMBDA,
    },
    ir::{Pattern, Symbol, WordEquation},
    sat::{nlit, pvar},
};

pub struct WordInEquationEncoder {
    lhs: Pattern,
    rhs: Pattern,
    match_lhs: PatternMatchingEncoder,
    match_rhs: PatternMatchingEncoder,
    word_encoding_lhs: Option<WordEncoding>,
    word_encoding_rhs: Option<WordEncoding>,
    mismatch_alo: IncrementalALO,
    lhs_bound: Option<usize>,
    rhs_bound: Option<usize>,
}

impl WordInEquationEncoder {
    pub fn new(eq: WordEquation) -> Self {
        let lhs = eq.lhs();
        let rhs = eq.rhs();
        let match_lhs = PatternMatchingEncoder::new(lhs.clone());
        let match_rhs = PatternMatchingEncoder::new(rhs.clone());

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

    fn encode_solution_words(&mut self, l_lhs: usize, l_rhs: usize) -> EncodingResult {
        let mut res = self.word_encoding_lhs.as_mut().unwrap().encode(l_lhs);
        res.extend(self.word_encoding_rhs.as_mut().unwrap().encode(l_rhs));
        res
    }

    fn encode_matching(&mut self, bounds: &Bounds, dom: &DomainEncoding) -> EncodingResult {
        let mut res = self
            .match_lhs
            .encode(&self.word_encoding_lhs.as_ref().unwrap(), bounds, dom);
        res.extend(
            self.match_rhs
                .encode(&self.word_encoding_rhs.as_ref().unwrap(), bounds, dom),
        );
        res
    }

    fn pattern_upper_bound(&self, pattern: &Pattern, bounds: &Bounds) -> usize {
        pattern
            .iter()
            .map(|s| match s {
                Symbol::Constant(_) => 1 as usize,
                Symbol::Variable(v) => {
                    bounds.get_upper_finite(v).expect("Upper bound not finite") as usize
                }
            })
            .sum()
    }

    fn lhs_upper_bound(&self, bounds: &Bounds) -> usize {
        self.pattern_upper_bound(&self.lhs, bounds)
    }

    fn rhs_upper_bound(&self, bounds: &Bounds) -> usize {
        self.pattern_upper_bound(&self.rhs, bounds)
    }

    /// Encodes that the word the lhs is mapped differs from the word the rhs is mapped to.
    fn encode_mismatch(
        &mut self,
        dom: &DomainEncoding,
        l_lhs: usize,
        l_rhs: usize,
    ) -> EncodingResult {
        let mut result = EncodingResult::empty();
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
                result.add_clause(vec![nlit(v), nlit(lhs_c), nlit(rhs_c)]);
            }
            let lhs_lambda = wlhs.at(pos, LAMBDA);
            let rhs_lambda = wrhs.at(pos, LAMBDA);

            result.add_clause(vec![nlit(v), nlit(lhs_lambda), nlit(rhs_lambda)]);
        }

        result.extend(self.mismatch_alo.add(&new_mismatch_selectors));

        result
    }
}

impl LiteralEncoder for WordInEquationEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.word_encoding_lhs.is_none() {
            self.word_encoding_lhs = Some(WordEncoding::new(dom.alphabet().clone()));
        }
        if self.word_encoding_rhs.is_none() {
            self.word_encoding_rhs = Some(WordEncoding::new(dom.alphabet().clone()));
        }

        // we allow both sides to map to any words in bounds
        // +1 is a technicality required by the encoding, see `encode_mismatch`
        let u_lhs = self.lhs_upper_bound(bounds) + 1;
        let u_rhs = self.rhs_upper_bound(bounds) + 1;
        let mut res = self.encode_solution_words(u_lhs, u_rhs);
        res.extend(self.encode_matching(bounds, dom));
        res.extend(self.encode_mismatch(dom, u_lhs, u_rhs));
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alphabet::Alphabet,
        bounds::Bounds,
        context::Context,
        encode::{domain::DomainEncoder, LiteralEncoder},
        ir::{parse_simple_equation, Substitutable, VarSubstitution, WordEquation},
        sat::plit,
    };

    use super::WordInEquationEncoder;

    fn solve_with_bounds(
        eq: &WordEquation,
        bounds: &[usize],
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        let alphabet: Alphabet =
            Alphabet::from_iter(eq.constants().iter().copied().chain('a'..='z'));
        let mut domain = DomainEncoder::new(alphabet);

        let mut cadical: cadical::Solver = cadical::Solver::default();

        let mut encoder = WordInEquationEncoder::new(eq.clone());

        for b in bounds {
            let mut bounds = Bounds::empty();
            for v in eq.variables() {
                bounds.set_upper(&v, (*b).into());
            }

            let mut res = domain.encode(&bounds, ctx);

            res.extend(encoder.encode(&bounds, domain.encoding()).unwrap());

            let assm = res.assumptions();

            for clause in res.into_inner().0.iter() {
                cadical.add_clause(clause.iter().copied());
            }
            match cadical.solve_with(assm.into_iter()) {
                Some(true) => {
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
                    for v in eq.variables() {
                        let mut found = false;
                        for l in 0..=*b {
                            let var = domain.encoding().string().get_len(&v, l).unwrap();
                            if cadical.value(plit(var)).unwrap_or(false) {
                                println!("\t|{}| = {}", v, l);
                                found = true;
                            }
                        }
                        assert!(found);
                    }
                    let subs = domain.encoding().get_model(&cadical);
                    return Some(subs);
                }
                Some(false) => continue,
                None => unreachable!(),
            }
        }
        None
    }

    fn assert_sat(eq: &WordEquation, bounds: &[usize], ctx: &mut Context) {
        match solve_with_bounds(eq, bounds, ctx) {
            Some(sol) => {
                let solved = eq.apply_substitution(&sol);
                assert!(
                    solved.lhs() != solved.rhs(),
                    "Returned substitution\n\t{}\nis not a solution for\n\t!({})",
                    sol,
                    eq
                );
            }
            None => panic!("Expected SAT"),
        }
    }

    fn assert_unsat(eq: &WordEquation, bounds: &[usize], ctx: &mut Context) {
        match solve_with_bounds(eq, bounds, ctx) {
            Some(sol) => {
                panic!("Expected UNSAT, got solution: {}", sol);
            }
            None => {}
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
