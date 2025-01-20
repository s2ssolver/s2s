use std::{collections::HashMap, rc::Rc};

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

use crate::{
    alphabet::Alphabet,
    bounds::Bounds,
    encode::{
        card::{exactly_one, IncrementalEO},
        EncodingResult, LAMBDA,
    },
    node::{canonical::Assignment, Sort, Sorted, Variable},
    sat::{nlit, plit, pvar, Cnf, PLit, PVar},
};

use super::DomainEncoding;

#[derive(Clone, Debug)]
pub struct StringDomain {
    substitutions: HashMap<(Rc<Variable>, usize, char), PVar>,
    lengths: IndexMap<(Variable, usize), PVar>,
}

impl StringDomain {
    pub fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
            lengths: IndexMap::new(),
        }
    }

    pub fn iter_substitutions(&self) -> impl Iterator<Item = (&Rc<Variable>, usize, char, &PVar)> {
        self.substitutions
            .iter()
            .map(|((var, pos, chr), v)| (var, *pos, *chr, v))
    }

    #[allow(dead_code)]
    pub fn iter_lengths(&self) -> impl Iterator<Item = (&Variable, usize, &PVar)> {
        self.lengths.iter().map(|((var, len), v)| (var, *len, v))
    }

    pub fn get_sub(&self, var: &Rc<Variable>, pos: usize, chr: char) -> Option<PVar> {
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
    pub(super) fn get_sub_lit(&self, var: &Rc<Variable>, pos: usize, chr: char) -> Option<PLit> {
        self.get_sub(var, pos, chr).map(plit)
    }

    pub(super) fn insert_substitution(
        &mut self,
        var: &Rc<Variable>,
        pos: usize,
        chr: char,
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

    pub(crate) fn get_model(&self, solver: &cadical::Solver, bounds: &Bounds) -> Assignment {
        let mut subs: HashMap<Rc<Variable>, Vec<Option<char>>> = HashMap::new();
        // initialize substitutions
        let vars = self.iter_substitutions().map(|(var, _, _, _)| var).unique();
        for var in vars {
            let len = bounds
                .get_upper_finite(var)
                .expect("Unbounded string variable");
            subs.insert(var.clone(), vec![None; len as usize]);
        }
        for (var, pos, chr, v) in self.iter_substitutions() {
            if let Some(true) = solver.value(plit(*v)) {
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
        let mut model = Assignment::default();
        for (var, sub) in subs.into_iter() {
            let mut s: Vec<char> = vec![];
            for c in sub.iter() {
                match c {
                    Some(LAMBDA) => {}
                    Some(c) => s.push(*c),
                    None => panic!("No substitution for {} at position {}", var, s.len()),
                }
            }
            let s = s.into_iter().collect::<String>();
            model.assign(var, s);
        }
        model
    }
}

pub(super) struct StringDomainEncoder {
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

    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    pub(super) fn encode(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        vars: &IndexSet<Rc<Variable>>,
    ) -> EncodingResult {
        let mut res = self.encode_substitutions(bounds, encoding, vars);
        res.extend(self.encode_str_lengths(bounds, encoding, vars));
        // Update last bound
        self.last_bounds = Some(bounds.clone());
        res
    }

    fn encode_substitutions(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        vars: &IndexSet<Rc<Variable>>,
    ) -> EncodingResult {
        let mut cnf = Cnf::new();
        let subs = &mut encoding.string;
        log::debug!("Encoding substitutions");

        // Encode the substitutions for each string variable
        for str_var in vars.iter().filter(|v| v.sort().is_string()) {
            let last_bound = self.pre_bounds(str_var).unwrap_or(0);
            let new_bound = bounds
                .get_upper_finite(str_var)
                .expect("Unbounded string variable") as usize;

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
        vars: &IndexSet<Rc<Variable>>,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        for str_var in vars.iter().filter(|v| v.sort().is_string()) {
            let mut len_choices = vec![];
            let last_bound = self.pre_bounds(str_var).map(|b| b + 1).unwrap_or(0);

            let lower = bounds
                .get_lower(str_var)
                .and_then(|f| f.as_num())
                .unwrap_or(0);
            debug_assert!(lower >= 0);
            let lower = lower as usize;

            if last_bound > 0 {
                let len = last_bound - 1;
                let choice = encoding.string().get_len(str_var, len).unwrap();
                // if the variable has this length, then only lambdas follow
                // we can only add this here because the following positions after last_bound - 1 were not yet defined in previous rounds
                if len < bounds.get_upper_finite(str_var).unwrap() as usize {
                    let lambda_suffix = encoding.string().get_sub(str_var, len, LAMBDA).unwrap();
                    res.add_clause(vec![nlit(choice), plit(lambda_suffix)]);
                }
            }

            for len in last_bound..=bounds.get_upper_finite(str_var).unwrap() as usize {
                let choice = pvar();
                len_choices.push(choice);
                // Deactive this lenght if it is less than the lower bound
                if len < lower {
                    res.add_clause(vec![nlit(choice)]);
                }
                encoding.string.insert_lenght(str_var.as_ref(), len, choice);

                // If the variable has this length, then only lambdas follow, and no lambdas precede
                if len < bounds.get_upper_finite(str_var).unwrap() as usize {
                    let lambda_suffix = encoding.string().get_sub(str_var, len, LAMBDA).unwrap();
                    res.add_clause(vec![nlit(choice), plit(lambda_suffix)]);
                }
                if len > 0 {
                    let lambda_prefix =
                        encoding.string().get_sub(str_var, len - 1, LAMBDA).unwrap();

                    res.add_clause(vec![nlit(choice), nlit(lambda_prefix)]);
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
        encode::{domain::DomainEncoding, LAMBDA},
        node::{NodeManager, Sort, Sorted},
        sat::plit,
    };

    use super::StringDomainEncoder;

    #[test]
    fn all_subst_defined() {
        let mut mngr = NodeManager::default();
        let var = mngr.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', LAMBDA]);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mb = 10;
        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, mb));

        let mut encoding = DomainEncoding::new(alphabet.clone(), bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &mngr.vars().cloned().collect());

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
        let mut mngr = NodeManager::default();
        let var = mngr.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', LAMBDA]);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());
        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, 5));

        let mut encoding = DomainEncoding::new(alphabet.clone(), bounds.clone());
        encoder.encode_substitutions(&bounds, &mut encoding, &mngr.vars().cloned().collect());
        bounds.set(var.as_ref().clone(), Interval::new(0, 10));
        encoder.encode_substitutions(&bounds, &mut encoding, &mngr.vars().cloned().collect());

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

        let mut mngr = NodeManager::default();
        let var = mngr.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());

        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode_substitutions(&bounds, &mut encoding, &mngr.vars().cloned().collect())
        {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = encoding.get_model(&solver);
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {})",
            len
        );
        let sub: String = subs.get(&var).cloned().unwrap().into();
        assert!(sub.len() == len as usize, "Substitution is too long");
        TestResult::passed()
    }

    #[quickcheck]
    fn incremental_solution_is_valid_substitution(len: u8) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        let mut mngr = NodeManager::default();
        let var = mngr.temp_var(Sort::String);

        let alphabet = Alphabet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = StringDomainEncoder::new(alphabet.clone());

        let mut bounds = Bounds::default();
        bounds.set(var.as_ref().clone(), Interval::new(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone());
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode_substitutions(
            &encoding.bounds.clone(),
            &mut encoding,
            &mngr.vars().cloned().collect(),
        ) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }
        encoding.bounds = update_bounds(&bounds, BoundStep::Double);
        match encoder.encode_substitutions(
            &encoding.bounds.clone(),
            &mut encoding,
            &mngr.vars().cloned().collect(),
        ) {
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
            for str_var in mngr.vars().filter(|v| v.sort().is_string()) {
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
            subs.contains_key(&var),
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
