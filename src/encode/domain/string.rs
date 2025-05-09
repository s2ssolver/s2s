use std::rc::Rc;

use indexmap::IndexMap;
use itertools::Itertools;

use rustsat::solvers::Solve;
use rustsat::{clause, types::Lit};
use rustsat_cadical::CaDiCaL;
use smt_str::{SmtChar, SmtString};

use crate::ast::VarSubstitution;
use crate::context::Context;
use crate::encode::EncodingSink;
use crate::{
    alphabet::Alphabet,
    context::{Sort, Sorted, Variable},
    domain::Domain,
    encode::{
        card::{exactly_one, IncrementalEO},
        EncodingResult, LAMBDA,
    },
    sat::{nlit, plit, pvar, PVar},
};

use super::DomainEncoding;

#[derive(Clone, Debug)]
pub struct StringDomain {
    substitutions: IndexMap<(Rc<Variable>, usize, SmtChar), PVar>,
    lengths: IndexMap<(Variable, usize), PVar>,
}

impl StringDomain {
    pub fn new() -> Self {
        Self {
            substitutions: IndexMap::new(),
            lengths: IndexMap::new(),
        }
    }

    pub fn iter_substitutions(
        &self,
    ) -> impl Iterator<Item = (&Rc<Variable>, usize, SmtChar, &PVar)> {
        self.substitutions
            .iter()
            .map(|((var, pos, chr), v)| (var, *pos, *chr, v))
    }

    #[allow(dead_code)]
    pub fn iter_lengths(&self) -> impl Iterator<Item = (&Variable, usize, &PVar)> {
        self.lengths.iter().map(|((var, len), v)| (var, *len, v))
    }

    pub fn get_sub(&self, var: &Rc<Variable>, pos: usize, chr: SmtChar) -> Option<PVar> {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.substitutions.get(&(var.clone(), pos, chr)).cloned()
    }

    pub fn get_len(&self, var: &Variable, len: usize) -> Option<PVar> {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.lengths.get(&(var.clone(), len)).cloned()
    }

    #[allow(dead_code)]
    pub(super) fn get_sub_lit(&self, var: &Rc<Variable>, pos: usize, chr: SmtChar) -> Option<Lit> {
        self.get_sub(var, pos, chr).map(plit)
    }

    pub(super) fn insert_substitution(
        &mut self,
        var: &Rc<Variable>,
        pos: usize,
        chr: SmtChar,
        v: PVar,
    ) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.substitutions.insert((var.clone(), pos, chr), v);
    }

    pub(super) fn insert_lenght(&mut self, var: &Variable, len: usize, v: PVar) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        let ok = self.lengths.insert((var.clone(), len), v);
        assert!(ok.is_none(), "Length {} already set for {}", len, var);
    }

    pub(crate) fn get_model(
        &self,
        solver: &CaDiCaL,
        bounds: &Domain,
        ctx: &mut Context,
    ) -> VarSubstitution {
        let mut subs: IndexMap<Rc<Variable>, Vec<Option<SmtChar>>> = IndexMap::new();
        // initialize substitutions
        let vars = self.iter_substitutions().map(|(var, _, _, _)| var).unique();
        for var in vars {
            let len = bounds
                .get_string(var)
                .and_then(|i| i.upper_finite())
                .expect("Unbounded string variable");
            subs.insert(var.clone(), vec![None; len as usize]);
        }
        let sol = solver.full_solution().unwrap();
        for (var, pos, chr, v) in self.iter_substitutions() {
            if sol.lit_value(plit(*v)).to_bool_with_def(false) {
                let sub = subs
                    .get_mut(var)
                    .unwrap_or_else(|| panic!("No substitution for {}", var));
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
        let mut model = VarSubstitution::default();
        for (var, sub) in subs.into_iter() {
            let mut s: Vec<SmtChar> = vec![];
            for c in sub.iter() {
                match c {
                    Some(LAMBDA) => {}
                    Some(c) => s.push(*c),
                    None => panic!("No substitution for {} at position {}", var, s.len()),
                }
            }
            let s = s.into_iter().collect::<SmtString>();
            model.add(var, ctx.ast().const_string(s));
        }
        model
    }
}

pub(super) struct StringDomainEncoder {
    last_dom: Option<Domain>,
    alphabet: Rc<Alphabet>,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's length.
    var_len_eo_encoders: IndexMap<Rc<Variable>, IncrementalEO>,
}

impl StringDomainEncoder {
    pub fn new(alphabet: Rc<Alphabet>) -> Self {
        Self {
            alphabet,
            last_dom: None,
            var_len_eo_encoders: IndexMap::new(),
        }
    }

    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    pub(super) fn encode(
        &mut self,
        bounds: &Domain,
        encoding: &mut DomainEncoding,
        sink: &mut impl EncodingSink,
    ) {
        self.encode_substitutions(bounds, encoding, sink);
        self.encode_str_lengths(bounds, encoding, sink);
        // Update last bound
        self.last_dom = Some(bounds.clone());
    }

    fn encode_substitutions(
        &mut self,
        dom: &Domain,
        encoding: &mut DomainEncoding,
        sink: &mut impl EncodingSink,
    ) {
        let subs = &mut encoding.string;
        log::debug!("Encoding substitutions");

        // Encode the substitutions for each string variable
        for (str_var, bound) in dom.iter_string() {
            debug_assert!(str_var.sort().is_string());
            let last_bound = self.pre_upper_bound(str_var).unwrap_or(0);
            let new_bound = bound.upper_finite().expect("Unbounded string variable") as usize;

            let alph = &self.alphabet;

            for b in last_bound..new_bound {
                let mut pos_subs = vec![];
                for c in alph.iter() {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    subs.insert_substitution(str_var, b, c, subvar);
                    pos_subs.push(subvar);
                }

                // Lambda (unused position = empty string)
                let subvar_lambda = pvar();
                subs.insert_substitution(str_var, b, LAMBDA, subvar_lambda);
                pos_subs.push(subvar_lambda);

                // If previous position is lambda, then so is this one
                if b > 0 {
                    let clause = clause![
                        nlit(subs.get_sub(str_var, b - 1, LAMBDA).unwrap_or_else(|| {
                            panic!("{:?}[{}] = {} undefined", str_var, b - 1, LAMBDA)
                        })),
                        plit(subvar_lambda)
                    ];
                    sink.add_clause(clause);
                }
                // Exactly one needs to be selected
                sink.add_cnf(exactly_one(&pos_subs));
            }
        }
    }

    fn encode_str_lengths(
        &mut self,
        dom: &Domain,
        encoding: &mut DomainEncoding,
        sink: &mut impl EncodingSink,
    ) {
        log::debug!("Encoding string lengths");

        for (str_var, bound) in dom.iter_string() {
            let mut len_choices = vec![];
            debug_assert!(str_var.sort().is_string());
            let last_bound = self.pre_upper_bound(str_var).map(|b| b + 1).unwrap_or(0);

            let lower = bound.lower_finite().unwrap_or(0);

            debug_assert!(lower >= 0, "Negative lower bound {} for {}", lower, str_var);
            let lower = lower as usize;
            let upper = bound.upper_finite().expect("Unbounded string variable") as usize;

            if last_bound > 0 {
                let len = last_bound - 1;
                let choice = encoding.string().get_len(str_var, len).unwrap();
                // if the variable has this length, then only lambdas follow
                // we can only add this here because the following positions after last_bound - 1 were not yet defined in previous rounds
                if len < upper {
                    let lambda_suffix = encoding.string().get_sub(str_var, len, LAMBDA).unwrap();
                    sink.add_clause(clause![nlit(choice), plit(lambda_suffix)]);
                }
            }

            for len in last_bound..=upper {
                let choice = pvar();
                len_choices.push(choice);
                // Deactive this lenght if it is less than the lower bound
                if len < lower {
                    //res.add_clause(vec![nlit(choice)]);
                    sink.add_assumption(nlit(choice));
                }
                encoding.string.insert_lenght(str_var.as_ref(), len, choice);

                // If the variable has this length, then only lambdas follow, and no lambdas precede
                if len < upper {
                    let lambda_suffix = encoding.string().get_sub(str_var, len, LAMBDA).unwrap();
                    sink.add_clause(clause![nlit(choice), plit(lambda_suffix)]);
                }
                if len > 0 {
                    let lambda_prefix =
                        encoding.string().get_sub(str_var, len - 1, LAMBDA).unwrap();

                    sink.add_clause(clause![nlit(choice), nlit(lambda_prefix)]);
                }
            }

            // Exactly one length must be true
            match self
                .var_len_eo_encoders
                .entry(str_var.clone())
                .or_default()
                .add(&len_choices)
            {
                EncodingResult::Cnf(cnf, asmpts) => {
                    sink.add_cnf(cnf);
                    for asmpt in asmpts {
                        sink.add_assumption(asmpt);
                    }
                }
                EncodingResult::Trivial(_) => (),
            }
        }
    }

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    /// Must be integer variable.
    fn pre_upper_bound(&self, var: &Variable) -> Option<usize> {
        debug_assert!(var.sort().is_string());
        match self.last_dom.as_ref() {
            Some(last_dom) => last_dom
                .get_string(var)
                .unwrap_or_else(|| panic!("Unbounded string variable: {:?}", var))
                .upper_finite()
                .map(|i| i as usize),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {

    use std::rc::Rc;

    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use rustsat_cadical::CaDiCaL;
    use smt_str::alphabet::CharRange;

    use crate::{
        alphabet::Alphabet,
        context::{Context, Sort},
        domain::Domain,
        encode::{domain::DomainEncoding, ResultSink, LAMBDA},
        interval::Interval,
    };
    use rustsat::solvers::Solve;

    use super::StringDomainEncoder;

    #[test]
    fn all_subst_defined() {
        let mut ctx = Context::default();
        let var = ctx.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a'.into(), 'b'.into(), 'c'.into(), LAMBDA]);
        let alphabet = Rc::new(alphabet);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mb = 10;
        let mut bounds = Domain::default();
        bounds.set_string(var.clone(), Interval::new(0, mb));

        let mut sink = ResultSink::default();
        let mut encoding = DomainEncoding::new(alphabet.clone(), bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &mut sink);

        for b in 0..mb {
            for c in alphabet.iter() {
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
        let var = ctx.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a'.into(), 'b'.into(), 'c'.into(), LAMBDA]);
        let alphabet = Rc::new(alphabet);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mut bounds = Domain::default();
        bounds.set_string(var.clone(), Interval::new(0, 5));
        let mut sink = ResultSink::default();
        let mut encoding = DomainEncoding::new(alphabet.clone(), bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &mut sink);
        bounds.set_string(var.clone(), Interval::new(0, 10));
        encoder.encode_substitutions(&bounds, &mut encoding, &mut sink);

        for b in 0..10 {
            for c in alphabet.iter() {
                assert!(encoding.string().get_sub_lit(&var, b, c).is_some());
            }
        }
    }

    #[quickcheck]
    fn solution_is_valid_substitution(len: u32) -> TestResult {
        let len = len % 20;
        if len == 0 {
            return TestResult::discard();
        }

        let mut ctx = Context::default();
        let var = ctx.temp_var(Sort::String);

        let mut alphabet = Alphabet::empty();
        alphabet.insert(CharRange::new('a', 'd'));
        let alphabet = Rc::new(alphabet);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());

        let mut bounds = Domain::default();
        bounds.set_string(var.clone(), Interval::new(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        let mut solver = CaDiCaL::default();

        let mut sink = ResultSink::default();
        encoder.encode_substitutions(&bounds, &mut encoding, &mut sink);

        match sink.result() {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                solver.add_cnf(cnf).unwrap();
                solver.solve().unwrap();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = encoding.get_model(&solver, &mut ctx);
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {})",
            len
        );
        let sub = subs.get(&var).and_then(|v| v.as_str_const()).unwrap();
        assert!(sub.len() == len as usize, "Substitution is too long");
        TestResult::passed()
    }

    #[quickcheck]
    #[ignore]
    fn incremental_solution_is_valid_substitution(len: u8) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        TestResult::passed()
    }
}
