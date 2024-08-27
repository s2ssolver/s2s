//! Encoding of the domains of all variables.

use indexmap::IndexMap;

use super::encoding::DomainEncoding;
use crate::{
    alphabet::Alphabet,
    bounds::{Bounds, Interval},
    context::Context,
    encode::{
        card::{exactly_one, IncrementalEO},
        EncodingResult, LAMBDA,
    },
    repr::Variable,
    sat::{nlit, plit, pvar, Cnf},
};

/// Encoder for the domains of all variables.
pub struct DomainEncoder {
    /// The encoder for string variables
    strings: StringDomainEncoder,
    /// The encoder for integer variables
    integers: IntegerEncoder,

    encoding: Option<DomainEncoding>,
}

impl DomainEncoder {
    pub fn new(alphabet: Alphabet) -> Self {
        Self {
            strings: StringDomainEncoder::new(alphabet),
            integers: IntegerEncoder::new(),
            encoding: None,
        }
    }

    pub fn encode(&mut self, bounds: &Bounds, ctx: &Context) -> EncodingResult {
        let mut encoding = self.encoding.take().unwrap_or(DomainEncoding::new(
            self.strings.alphabet.clone(),
            bounds.clone(),
        ));

        let mut res = self.strings.encode(bounds, &mut encoding, ctx);

        res.extend(self.integers.encode(bounds, &mut encoding, ctx));
        encoding.bounds = bounds.clone();
        self.encoding = Some(encoding);
        res
    }

    pub fn encoding(&self) -> &DomainEncoding {
        self.encoding.as_ref().unwrap()
    }

    pub fn reset(&mut self) {
        self.strings.reset();
        self.integers.reset();
        self.encoding = None;
    }
}

// TODO: Encode lengths here.
pub struct StringDomainEncoder {
    last_bounds: Option<Bounds>,
    alphabet: Alphabet,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's length.
    var_len_eo_encoders: IndexMap<Variable, IncrementalEO>,
}

impl StringDomainEncoder {
    pub fn new(alphabet: Alphabet) -> Self {
        Self {
            alphabet,
            last_bounds: None,
            var_len_eo_encoders: IndexMap::new(),
        }
    }

    pub fn reset(&mut self) {
        self.last_bounds = None;
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        ctx: &Context,
    ) -> EncodingResult {
        let mut res = self.encode_substitutions(bounds, encoding, ctx);
        res.extend(self.encode_str_lengths(bounds, encoding, ctx));
        // Update last bound
        self.last_bounds = Some(bounds.clone());
        res
    }

    fn encode_substitutions(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        ctx: &Context,
    ) -> EncodingResult {
        let mut cnf = Cnf::new();
        let subs = &mut encoding.string;
        log::debug!("Encoding substitutions");

        // Encode the substitutions for each string variable
        for str_var in ctx.string_vars() {
            let last_bound = self.pre_bounds(&str_var).unwrap_or(0);
            let new_bound = bounds
                .get_upper_finite(&str_var)
                .expect("Unbounded string variable") as usize;

            let alph = &self.alphabet;
            for b in last_bound..new_bound {
                let mut pos_subs = vec![];
                for c in alph.iter() {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    subs.inser_substitution(str_var, b, c, subvar);
                    pos_subs.push(subvar)
                }

                // Lambda (unused position = empty string)
                let subvar_lambda = pvar();
                subs.inser_substitution(str_var, b, LAMBDA, subvar_lambda);
                pos_subs.push(subvar_lambda);

                // If previous position is lambda, then so is this one
                if b > 0 {
                    let clause = vec![
                        nlit(subs.get_sub(str_var, b - 1, LAMBDA).unwrap_or_else(|| {
                            panic!("{:?}[{}] = {} undefined", str_var, b - 1, LAMBDA)
                        })),
                        plit(subvar_lambda),
                    ];
                    cnf.push(clause);
                }
                // Exactly one needs to be selected
                cnf.extend(exactly_one(&pos_subs));
            }
        }

        EncodingResult::cnf(cnf)
    }

    fn encode_str_lengths(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        ctx: &Context,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        for str_var in ctx.string_vars() {
            let mut len_choices = vec![];
            let last_bound = self.pre_bounds(&str_var).map(|b| b + 1).unwrap_or(0);

            let lower = bounds
                .get_lower(&str_var)
                .and_then(|f| f.as_num())
                .unwrap_or(0);
            debug_assert!(lower >= 0);
            let lower = lower as usize;
            for len in last_bound..=bounds.get_upper_finite(&str_var).unwrap() as usize {
                let choice = pvar();
                len_choices.push(choice);
                // Deactive this lenght if it is less than the lower bound
                if len < lower {
                    res.add_clause(vec![nlit(choice)]);
                }
                encoding.string.insert_lenght(str_var.as_ref(), len, choice);

                // If the variable has this length, then only lambdas follow, and no lambdas precede
                if len < bounds.get_upper_finite(&str_var).unwrap() as usize {
                    let lambda_suffix = encoding
                        .string()
                        .get_sub(str_var, len as usize, LAMBDA)
                        .unwrap();
                    res.add_clause(vec![nlit(choice), plit(lambda_suffix)]);
                }
                if len > 0 {
                    let not_lambda_prefix = encoding
                        .string()
                        .get_sub(str_var, len as usize - 1, LAMBDA)
                        .unwrap();
                    res.add_clause(vec![nlit(choice), nlit(not_lambda_prefix)]);
                }
            }

            // Exactly one length must be true
            let eo = self
                .var_len_eo_encoders
                .entry(str_var.as_ref().clone())
                .or_default()
                .add(&len_choices);

            res.extend(eo);
        }

        res
    }

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    /// Must be integer variable.
    fn pre_bounds(&self, var: &Variable) -> Option<usize> {
        self.last_bounds
            .as_ref()
            .map(|bs| bs.get_upper_finite(var).expect("Unbounded string variable") as usize)
    }
}

pub struct IntegerEncoder {
    last_domains: Option<Bounds>,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's domain.
    var_len_eo_encoders: IndexMap<Variable, IncrementalEO>,
}

impl IntegerEncoder {
    pub fn new() -> Self {
        Self {
            last_domains: None,
            var_len_eo_encoders: IndexMap::new(),
        }
    }

    pub fn reset(&mut self) {
        self.last_domains = None;
        self.var_len_eo_encoders.clear();
    }

    pub fn encode(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        ctx: &Context,
    ) -> EncodingResult {
        let res = self.encode_int_vars(bounds, encoding, ctx);

        self.last_domains = Some(bounds.clone());
        res
    }

    fn get_last_dom(&self, var: &Variable) -> Option<Interval> {
        self.last_domains.as_ref().and_then(|doms| doms.get(var))
    }

    fn encode_int_vars(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        ctx: &Context,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        for int_var in ctx.int_vars() {
            let mut len_choices = vec![];
            let last_upper_bound = self
                .get_last_dom(int_var)
                .map(|b| (b.upper_finite().unwrap()));
            // from last_upper_bound to upper bound
            let last_lower_bound = self
                .get_last_dom(int_var)
                .map(|b| b.lower_finite().unwrap());

            let lower = bounds.get_lower_finite(int_var).unwrap_or(0);
            let upper = bounds.get_upper_finite(int_var).unwrap();
            for len in lower..=upper {
                if last_lower_bound.map(|ll| len < ll).unwrap_or(true)
                    || last_upper_bound.map(|lu| len > lu).unwrap_or(true)
                {
                    // This lenght is not in the previous domain, so we need to encode it
                    let choice = pvar();
                    len_choices.push(choice);
                    encoding
                        .int
                        .insert(int_var.as_ref().clone(), len as isize, choice);
                }
            }
            // Exactly one length must be true
            let eo = self
                .var_len_eo_encoders
                .entry(int_var.as_ref().clone())
                .or_default()
                .add(&len_choices);

            res.extend(eo);
        }
        res
    }
}

#[cfg(test)]
mod tests {

    use std::collections::HashMap;

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::{
        alphabet::Alphabet,
        bounds::{
            step::{update_bounds, BoundStep},
            Bounds, Interval,
        },
        context::Context,
        encode::{
            domain::encoding::{get_str_substitutions, DomainEncoding},
            LAMBDA,
        },
        repr::Sort,
        sat::plit,
    };

    use super::StringDomainEncoder;

    #[test]
    fn all_subst_defined() {
        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c']);
        let mut alphabet_lambda = alphabet.clone();
        alphabet_lambda.insert_char(LAMBDA);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mb = 10;
        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, mb));

        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &ctx);

        for b in 0..mb {
            for c in alphabet_lambda.iter() {
                assert!(
                    encoding.string().get_sub_lit(&var, b as usize, c).is_some(),
                    "{:?}[{}] = {} not defined {:?}",
                    var,
                    b,
                    c,
                    encoding.string()
                );
            }
        }
    }

    #[test]
    fn all_subst_defined_incremental() {
        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c']);
        let mut alphabet_lambda = alphabet.clone();
        alphabet_lambda.insert_char(LAMBDA);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, 5));

        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &ctx);
        bounds.set(var.as_ref().clone(), Interval::new(0, 10));
        encoder.encode_substitutions(&bounds, &mut encoding, &ctx);

        for b in 0..10 {
            for c in alphabet_lambda.iter() {
                assert!(encoding.string().get_sub_lit(&var, b, c).is_some());
            }
        }
    }

    #[quickcheck]
    fn solution_is_valid_substitution(len: u32) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        let len = len % 20;

        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());

        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode_substitutions(&bounds, &mut encoding, &ctx) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = get_str_substitutions(&encoding, &ctx, &solver);
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {})",
            len
        );
        let sub = subs.get(&var).unwrap();
        assert!(sub.len() == len as usize, "Substitution is too long");
        TestResult::passed()
    }

    #[quickcheck]
    fn incremental_solution_is_valid_substitution(len: u8) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());

        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode_substitutions(&encoding.bounds.clone(), &mut encoding, &ctx) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }
        encoding.bounds = update_bounds(&bounds, BoundStep::Double);
        match encoder.encode_substitutions(&encoding.bounds.clone(), &mut encoding, &ctx) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = {
            let domain_encoding = &encoding;

            let solver = &solver;
            if solver.status() != Some(true) {
                panic!("Solver is not in a SAT state")
            }
            let mut subs = HashMap::new();
            for str_var in ctx.string_vars() {
                // initialize substitutions
                subs.insert(
                    str_var.clone(),
                    vec![
                        None;
                        domain_encoding
                            .bounds
                            .get_upper_finite(str_var)
                            .expect("Unbounded string variable") as usize
                    ],
                );
            }
            for (var, pos, chr, v) in domain_encoding.string().iter_substitutions() {
                if let Some(true) = solver.value(plit(*v)) {
                    let sub = subs.get_mut(var).unwrap();
                    // This could be more efficient by going over the positions only once, however, this way we can check for invalid substitutions
                    assert!(
                        sub[pos].is_none(),
                        "Multiple substitutions for {} at position {}",
                        var,
                        pos
                    );

                    sub[pos] = Some(chr);
                }
            }
            let mut subs_str = HashMap::new();
            for (var, sub) in subs.into_iter() {
                let mut s = vec![];
                for c in sub.iter() {
                    match c {
                        Some(LAMBDA) => {}
                        Some(c) => s.push(*c),
                        None => panic!("No substitution for {} at position {}", var, s.len()),
                    }
                }
                subs_str.insert(var.clone(), s);
            }
            subs_str
        };
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {}) {:?}",
            len,
            subs
        );
        let sub = subs.get(&var).unwrap();
        let expected_len = (len as usize) * 2;
        assert!(
            sub.len() <= expected_len,
            "Expected length {}, got {}: {:?}",
            expected_len,
            sub.len(),
            sub
        );
        TestResult::passed()
    }
}
