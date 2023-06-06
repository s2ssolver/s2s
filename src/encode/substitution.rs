use indexmap::{IndexMap, IndexSet};

use super::{
    card::{exactly_one, IncrementalEO},
    EncodingResult,
};
use crate::{
    encode::LAMBDA,
    model::Variable,
    sat::{as_lit, neg, pvar, Cnf, PLit, PVar},
};
use std::collections::HashMap;

use super::VariableBounds;

#[derive(Clone, Debug)]
pub struct SubstitutionEncoding {
    encodings: HashMap<(Variable, usize, char), PVar>,
    length: IndexMap<(Variable, usize), PVar>,
    bounds: VariableBounds,
    alphabet: IndexSet<char>,
}

impl SubstitutionEncoding {
    pub fn new(alphabet: IndexSet<char>, bounds: VariableBounds) -> Self {
        Self {
            encodings: HashMap::new(),
            length: IndexMap::new(),
            alphabet,
            bounds,
        }
    }

    pub fn get(&self, var: &Variable, pos: usize, chr: char) -> Option<PVar> {
        self.encodings.get(&(var.clone(), pos, chr)).cloned()
    }

    pub fn get_len(&self, var: &Variable, len: usize) -> Option<PVar> {
        self.length.get(&(var.clone(), len)).cloned()
    }

    pub fn get_lit(&self, var: &Variable, pos: usize, chr: char) -> Option<PLit> {
        self.get(var, pos, chr).map(as_lit)
    }

    fn add(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        self.encodings.insert((var.clone(), pos, chr), v);
    }

    #[allow(dead_code)]
    pub fn alphabet(&self) -> &IndexSet<char> {
        &self.alphabet
    }

    pub fn alphabet_lambda(&self) -> IndexSet<char> {
        let l: IndexSet<char> = IndexSet::from_iter(vec![LAMBDA]);
        self.alphabet.union(&l).cloned().collect()
    }

    fn vars(&self) -> IndexSet<&Variable> {
        self.encodings.keys().map(|(v, _, _)| v).collect()
    }

    /// Reads the substitutions from the model.
    /// Panics if the solver is not in a SAT state.
    #[allow(dead_code)]
    pub fn get_substitutions(&self, solver: &cadical::Solver) -> HashMap<Variable, Vec<char>> {
        if solver.status() != Some(true) {
            panic!("Solver is not in a SAT state")
        }
        let mut subs = HashMap::new();
        for var in self.vars() {
            // initialize substitutions
            subs.insert(var.clone(), vec![None; self.bounds.get(var)]);
        }
        for ((var, pos, chr), _v) in self.encodings.iter() {
            if let Some(true) = solver.value(as_lit(self.get(var, *pos, *chr).unwrap())) {
                let sub = subs.get_mut(var).unwrap();
                // This could be more efficient by going over the positions only once, however, this way we can check for invalid substitutions
                assert!(
                    sub[*pos].is_none(),
                    "Multiple substitutions for {} at position {}",
                    var,
                    pos
                );

                sub[*pos] = Some(*chr);
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
    }
}

pub struct SubstitutionEncoder {
    encoding: Option<SubstitutionEncoding>,
    vars: IndexSet<Variable>,
    last_bounds: Option<VariableBounds>,
    alphabet: IndexSet<char>,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's length.
    var_len_eo_encoders: IndexMap<Variable, IncrementalEO>,
    // If true, then no lambda substitutions are allowed
    singular: bool,
}

impl SubstitutionEncoder {
    pub fn new(alphabet: IndexSet<char>, vars: IndexSet<Variable>) -> Self {
        Self {
            var_len_eo_encoders: IndexMap::new(),
            encoding: None,
            vars,
            alphabet,
            last_bounds: None,
            singular: false,
        }
    }

    /// Sets the Boolean variable that is true if the variable has the given length.
    /// Panics if the variable was already set.
    fn set_var_len(&mut self, var: &Variable, len: usize, var_len: PVar) {
        let res = self
            .encoding
            .as_mut()
            .unwrap()
            .length
            .insert((var.clone(), len), var_len);
        assert!(res.is_none());
    }

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    fn get_last_var_bound(&self, var: &Variable) -> Option<usize> {
        self.last_bounds.as_ref().map(|bounds| bounds.get(var))
    }

    /// Encodes the possible lengths of each variable. Any variable might have exactly one length up to its bound.
    fn encode_var_lengths(&mut self, bounds: &VariableBounds) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let vars: Vec<Variable> = self.vars.iter().cloned().collect();
        for v in vars {
            let mut len_choices = vec![];
            let last_bound = self.get_last_var_bound(&v).map(|b| b + 1).unwrap_or(0);

            for len in last_bound..=bounds.get(&v) {
                let choice = pvar();
                len_choices.push(choice);

                self.set_var_len(&v, len, choice);
                // If the variable has this length, then only lambdas follow, and no lambdas precede
                if !self.singular {
                    if len < bounds.get(&v) {
                        let lambda_suffix = self
                            .encoding
                            .as_ref()
                            .unwrap()
                            .get(&v, len, LAMBDA)
                            .unwrap();
                        res.add_clause(vec![neg(choice), as_lit(lambda_suffix)]);
                    }
                    if len > 0 {
                        let not_lambda_prefix = self
                            .get_encoding()
                            .unwrap()
                            .get(&v, len - 1, LAMBDA)
                            .unwrap();
                        res.add_clause(vec![neg(choice), neg(not_lambda_prefix)]);
                    }
                }
            }

            // Exactly one length must be true
            let eo = self
                .var_len_eo_encoders
                .entry(v.clone())
                .or_default()
                .add(&len_choices);

            res.join(eo);
        }

        res
    }

    pub fn encode(&mut self, bounds: &VariableBounds) -> EncodingResult {
        let mut cnf = Cnf::new();
        if self.encoding.is_none() {
            self.encoding = Some(SubstitutionEncoding::new(
                self.alphabet.clone(),
                bounds.clone(),
            ));
        }
        log::debug!("Encoding substitutions");
        for var in &self.vars {
            let bound = bounds.get(var);
            let last_bound = self.pre_bounds(var).unwrap_or(0);
            let encoding = self.encoding.as_mut().unwrap();
            encoding.bounds = bounds.clone();
            // Todo: this is bad because it clones the alphabet
            let alph = self.alphabet.clone();
            for b in last_bound..bound {
                let mut pos_subs = vec![];
                for c in &alph {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    encoding.add(var, b, *c, subvar);
                    pos_subs.push(subvar)
                }
                if !self.singular {
                    // Lambda
                    let subvar_lambda = pvar();
                    encoding.add(var, b, LAMBDA, subvar_lambda);
                    pos_subs.push(subvar_lambda);

                    // If previous position is lambda, then so is this one
                    if b > 0 {
                        let clause = vec![
                            neg(encoding.get(var, b - 1, LAMBDA).unwrap()),
                            as_lit(subvar_lambda),
                        ];
                        cnf.push(clause);
                    }
                }
                // Exactly one needs to be selected
                cnf.extend(exactly_one(&pos_subs));
            }
        }
        let mut res = EncodingResult::cnf(cnf);
        res.join(self.encode_var_lengths(bounds));

        self.last_bounds = Some(bounds.clone());
        res
    }

    fn pre_bounds(&self, var: &Variable) -> Option<usize> {
        self.last_bounds.as_ref().map(|bs| bs.get(var))
    }

    /// Returns the encoding for the substitutions.
    /// Returns `None` if the encoding has not been created yet, i.e., if `encode` has not been called.
    pub fn get_encoding(&self) -> Option<&SubstitutionEncoding> {
        self.encoding.as_ref()
    }
}

#[cfg(test)]
mod tests {

    use indexmap::IndexSet;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::{encode::VariableBounds, model::VarManager};

    use super::SubstitutionEncoder;

    #[test]
    fn all_subst_defined() {
        let mut vm = VarManager::new();
        let var = vm.tmp_var(crate::model::Sort::String);
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c']);
        let vars = IndexSet::from_iter(vec![var.clone()]);
        let mut encoder = SubstitutionEncoder::new(alphabet, vars);
        let mb = 10;
        let bounds = VariableBounds::new(mb);

        encoder.encode(&bounds);

        for b in 0..mb {
            for c in encoder.get_encoding().unwrap().alphabet_lambda() {
                assert!(encoder
                    .get_encoding()
                    .unwrap()
                    .get_lit(&var, b, c)
                    .is_some());
            }
        }
    }

    #[test]
    fn all_subst_defined_incremental() {
        let mut vm = VarManager::new();
        let var = vm.tmp_var(crate::model::Sort::String);
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c']);
        let vars = IndexSet::from_iter(vec![var.clone()]);
        let mut encoder = SubstitutionEncoder::new(alphabet, vars);

        let bounds = VariableBounds::new(5);
        encoder.encode(&bounds);
        let bounds = VariableBounds::new(10);
        encoder.encode(&bounds);

        for b in 0..10 {
            for c in encoder.get_encoding().unwrap().alphabet_lambda() {
                assert!(encoder
                    .get_encoding()
                    .unwrap()
                    .get_lit(&var, b, c)
                    .is_some());
            }
        }
    }

    #[quickcheck]
    fn solution_is_valid_substitution(len: u8) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        let mut vm = VarManager::new();
        let var = vm.tmp_var(crate::model::Sort::String);
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c', 'd']);
        let vars = IndexSet::from_iter(vec![var.clone()]);
        let mut encoder = SubstitutionEncoder::new(alphabet, vars);
        encoder.singular = true;

        let bounds = VariableBounds::new(len as usize);
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode(&bounds) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = encoder.get_encoding().unwrap().get_substitutions(&solver);
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
        let mut vm = VarManager::new();
        let var = vm.tmp_var(crate::model::Sort::String);
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c', 'd']);
        let vars = IndexSet::from_iter(vec![var.clone()]);
        let mut encoder = SubstitutionEncoder::new(alphabet, vars);

        let mut bounds = VariableBounds::new(len as usize);
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode(&bounds) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }
        bounds.double(None);
        match encoder.encode(&bounds) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = encoder.get_encoding().unwrap().get_substitutions(&solver);
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {})",
            len
        );
        let sub = subs.get(&var).unwrap();
        let expected_len = (len as usize) * 2;
        assert!(
            sub.len() == expected_len,
            "Expected length {}, got {}: {:?}",
            expected_len,
            sub.len(),
            sub
        );
        TestResult::passed()
    }
}
