//! Encoding of the domains of all variables.

use indexmap::{IndexMap, IndexSet};

use super::{card::IncrementalEO, EncodingResult};
use crate::{
    bounds::{Bounds, IntDomain},
    encode::{card::exactly_one, LAMBDA},
    instance::Instance,
    model::{Sort, Variable},
    sat::{as_lit, neg, pvar, Cnf, PLit, PVar},
};
use std::collections::HashMap;

/// Encoder for the domains of all variables.
pub struct DomainEncoder {
    /// The encoder for string variables
    strings: SubstitutionEncoder,
    /// The encoder for integer variables
    integers: IntegerEncoder,

    /// Maps each variable of sort `Bool` to a propositional variable
    bools: IndexMap<Variable, PVar>,

    encoding: Option<DomainEncoding>,
}

impl DomainEncoder {
    pub fn new(alphabet: IndexSet<char>) -> Self {
        Self {
            strings: SubstitutionEncoder::new(alphabet),
            integers: IntegerEncoder::new(),
            bools: IndexMap::new(),
            encoding: None,
        }
    }

    /// Encodes the boolean variables by instantiating a new propositional variable for each variable of sort `Bool`.
    /// This method only needs to be called whenever the set of boolean variables changes (usuall only once).
    /// However, it is safe to call it multiple times as it is idempotent for the same set of variables.
    pub fn init_booleans(&mut self, instance: &Instance) {
        for v in instance.vars_of_sort(Sort::Bool) {
            if self.bools.get(v).is_some() {
                continue;
            }
            self.bools.insert(v.clone(), pvar());
        }
    }

    pub fn encode(&mut self, bounds: &Bounds, instance: &Instance) -> EncodingResult {
        let mut encoding = self.encoding.take().unwrap_or(DomainEncoding::new(
            self.strings.alphabet.clone(),
            bounds.clone(),
            false,
        ));
        let mut res = EncodingResult::empty();
        res.join(self.strings.encode(bounds, &mut encoding, instance));
        res.join(self.integers.encode(bounds, &mut encoding, instance));
        encoding.bounds = bounds.clone();
        self.encoding = Some(encoding);
        res
    }

    pub fn encoding(&self) -> &DomainEncoding {
        self.encoding.as_ref().unwrap()
    }

    pub fn get_bools(&self) -> &IndexMap<Variable, PVar> {
        &self.bools
    }
}

#[derive(Clone, Debug, Default)]
pub struct IntEncoding {
    encodings: IndexMap<(Variable, isize), PVar>,
}

impl IntEncoding {
    /// Sets the Boolean variable that is true if the variable has the given length.
    /// Panics if the variable was already set.
    pub fn insert(&mut self, var: Variable, value: isize, pvar: PVar) {
        assert!(
            var.sort() == Sort::Int,
            "Variable {} is not an integer",
            var
        );
        let ok = self.encodings.insert((var, value), pvar);
        assert!(ok.is_none());
    }

    pub fn get(&self, var: &Variable, value: isize) -> Option<PVar> {
        assert!(
            var.sort() == Sort::Int,
            "Variable {} is not an integer",
            var
        );
        self.encodings.get(&(var.clone(), value)).cloned()
    }
}

#[derive(Clone, Debug)]
pub struct SubstitutionEncoding {
    encodings: HashMap<(Variable, usize, char), PVar>,
}

impl SubstitutionEncoding {
    pub fn new() -> Self {
        Self {
            encodings: HashMap::new(),
        }
    }

    pub fn get(&self, var: &Variable, pos: usize, chr: char) -> Option<PVar> {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.encodings.get(&(var.clone(), pos, chr)).cloned()
    }

    pub fn get_lit(&self, var: &Variable, pos: usize, chr: char) -> Option<PLit> {
        self.get(var, pos, chr).map(as_lit)
    }

    fn add(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.encodings.insert((var.clone(), pos, chr), v);
    }
}

/// Propositional encoding of the domains of all variables.
pub struct DomainEncoding {
    /// The encoding of the substitutions
    string: SubstitutionEncoding,
    /// The encoding of the integer domains
    int: IntEncoding,

    /// The alphabet used for the substitutions
    alphabet: IndexSet<char>,
    /// If true, then no lambda substitutions are allowed
    singular: bool,
    /// The bounds of the integer variables
    bounds: Bounds,
}

impl DomainEncoding {
    pub fn new(alphabet: IndexSet<char>, bounds: Bounds, singular: bool) -> Self {
        Self {
            string: SubstitutionEncoding::new(),
            int: IntEncoding::default(),
            alphabet,
            singular,
            bounds,
        }
    }

    pub fn string(&self) -> &SubstitutionEncoding {
        &self.string
    }

    pub fn int(&self) -> &IntEncoding {
        &self.int
    }

    pub fn alphabet(&self) -> &IndexSet<char> {
        &self.alphabet
    }

    pub fn alphabet_lambda(&self) -> IndexSet<char> {
        let mut alph = self.alphabet.clone();
        alph.insert(LAMBDA);
        alph
    }
}

/// Reads the substitutions from the model.
/// Panics if the solver is not in a SAT state.
/// TODO: Move this into the SubstitutionEncoding struct
pub fn get_substitutions(
    domain_encoding: &DomainEncoding,
    instance: &Instance,
    solver: &cadical::Solver,
) -> HashMap<Variable, Vec<char>> {
    if solver.status() != Some(true) {
        panic!("Solver is not in a SAT state")
    }
    let mut subs = HashMap::new();
    for var in instance.vars_of_sort(Sort::String) {
        // initialize substitutions
        let len_var = &var.len_var().unwrap();
        subs.insert(
            var.clone(),
            vec![
                None;
                domain_encoding
                    .bounds
                    .get_upper(len_var)
                    .expect("Unbounded string variable") as usize
            ],
        );
    }
    for ((var, pos, chr), v) in domain_encoding.string.encodings.iter() {
        if let Some(true) = solver.value(as_lit(*v)) {
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

pub struct SubstitutionEncoder {
    last_bounds: Option<Bounds>,
    alphabet: IndexSet<char>,

    // If true, then no lambda substitutions are allowed
    singular: bool,
}

impl SubstitutionEncoder {
    pub fn new(alphabet: IndexSet<char>) -> Self {
        Self {
            alphabet,
            last_bounds: None,
            singular: false,
        }
    }

    pub fn encode(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        instance: &Instance,
    ) -> EncodingResult {
        let mut cnf = Cnf::new();
        let subs = &mut encoding.string;
        log::debug!("Encoding substitutions");

        for str_var in instance.vars_of_sort(Sort::String) {
            let var = str_var
                .len_var()
                .unwrap_or_else(|| panic!("No length variable for {}", str_var));
            let bound = bounds.get_upper(&var).expect("Unbounded string variable") as usize;
            let last_bound = self.pre_bounds(&var).unwrap_or(0);

            // Todo: this is bad because it clones the alphabet
            let alph = self.alphabet.clone();
            for b in last_bound..bound {
                let mut pos_subs = vec![];
                for c in &alph {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    subs.add(str_var, b, *c, subvar);
                    pos_subs.push(subvar)
                }
                if !self.singular {
                    // Lambda
                    let subvar_lambda = pvar();
                    subs.add(str_var, b, LAMBDA, subvar_lambda);
                    pos_subs.push(subvar_lambda);

                    // If previous position is lambda, then so is this one
                    if b > 0 {
                        let clause = vec![
                            neg(subs.get(str_var, b - 1, LAMBDA).unwrap_or_else(|| {
                                panic!("{:?}[{}] = {} undefined", str_var, b - 1, LAMBDA)
                            })),
                            as_lit(subvar_lambda),
                        ];
                        cnf.push(clause);
                    }
                }
                // Exactly one needs to be selected
                cnf.extend(exactly_one(&pos_subs));
            }
        }

        self.last_bounds = Some(bounds.clone());
        EncodingResult::cnf(cnf)
    }

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    /// Must be integer variable.
    fn pre_bounds(&self, var: &Variable) -> Option<usize> {
        self.last_bounds
            .as_ref()
            .map(|bs| bs.get_upper(var).expect("Unbounded string variable") as usize)
    }
}

pub struct IntegerEncoder {
    last_domains: Option<Bounds>,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's length.
    var_len_eo_encoders: IndexMap<Variable, IncrementalEO>,
}

impl IntegerEncoder {
    pub fn new() -> Self {
        Self {
            last_domains: None,
            var_len_eo_encoders: IndexMap::new(),
        }
    }

    pub fn encode(
        &mut self,
        domains: &Bounds,
        encoding: &mut DomainEncoding,
        instance: &Instance,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();
        for v in instance.vars_of_sort(Sort::Int) {
            if v.is_len_var() {
                continue;
            } else {
                todo!("Integer variables not supported yet")
            }
        }
        res.join(self.encode_str_lengths(domains, encoding, instance));
        self.last_domains = Some(domains.clone());
        res
    }

    fn get_last_dom(&self, var: &Variable) -> Option<IntDomain> {
        self.last_domains.as_ref().map(|doms| doms.get(var))
    }

    pub fn encode_str_lengths(
        &mut self,
        bounds: &Bounds,
        encoding: &mut DomainEncoding,
        instance: &Instance,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        for str_var in instance.vars_of_sort(Sort::String) {
            let str_len_var = str_var.len_var().unwrap();
            let mut len_choices = vec![];
            let last_bound = self
                .get_last_dom(&str_len_var)
                .map(|b| (b.get_upper().unwrap()) + 1)
                .unwrap_or(0);

            let lower = bounds.get_lower(&str_len_var).unwrap_or(0);
            for len in last_bound..=bounds.get_upper(&str_len_var).unwrap() {
                let choice = pvar();
                len_choices.push(choice);
                // Deactive this lenght if it is less than the lower bound
                if len < lower {
                    res.add_clause(vec![neg(choice)]);
                }
                encoding.int.insert(str_len_var.clone(), len, choice);
                // If the variable has this length, then only lambdas follow, and no lambdas precede
                if !encoding.singular {
                    if len < bounds.get_upper(&str_len_var).unwrap() {
                        let lambda_suffix = encoding
                            .string()
                            .get(str_var, len as usize, LAMBDA)
                            .unwrap();
                        res.add_clause(vec![neg(choice), as_lit(lambda_suffix)]);
                    }
                    if len > 0 {
                        let not_lambda_prefix = encoding
                            .string()
                            .get(str_var, len as usize - 1, LAMBDA)
                            .unwrap();
                        res.add_clause(vec![neg(choice), neg(not_lambda_prefix)]);
                    }
                }
            }

            // Exactly one length must be true
            let eo = self
                .var_len_eo_encoders
                .entry(str_len_var.clone())
                .or_default()
                .add(&len_choices);

            res.join(eo);
        }

        res
    }
}

#[cfg(test)]
mod tests {

    use indexmap::IndexSet;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    use crate::{
        bounds::{Bounds, IntDomain},
        encode::{
            domain::{get_substitutions, DomainEncoding},
            LAMBDA,
        },
        instance::Instance,
        model::{Sort, Variable},
    };

    use super::SubstitutionEncoder;

    #[test]
    fn all_subst_defined() {
        let mut instance = Instance::default();
        let var = Variable::temp(Sort::String);
        instance.add_var(var.clone());

        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c']);
        let mut alphabet_lambda = alphabet.clone();
        alphabet_lambda.insert(LAMBDA);

        let mut encoder = SubstitutionEncoder::new(alphabet.clone());
        let mb = 10;
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, mb));

        let mut encoding = DomainEncoding::new(alphabet, bounds.clone(), false);
        encoder.encode(&bounds, &mut encoding, &instance);

        for b in 0..mb {
            for c in &alphabet_lambda {
                assert!(
                    encoding.string().get_lit(&var, b as usize, *c).is_some(),
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
        let mut instance = Instance::default();
        let var = Variable::temp(Sort::String);
        instance.add_var(var.clone());
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c']);
        let mut alphabet_lambda = alphabet.clone();
        alphabet_lambda.insert(LAMBDA);

        let mut encoder = SubstitutionEncoder::new(alphabet.clone());
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 5));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone(), false);
        encoder.encode(&bounds, &mut encoding, &instance);
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, 10));
        encoder.encode(&bounds, &mut encoding, &instance);

        for b in 0..10 {
            for c in &alphabet_lambda {
                assert!(encoding.string().get_lit(&var, b, *c).is_some());
            }
        }
    }

    #[quickcheck]
    fn solution_is_valid_substitution(len: u8) -> TestResult {
        if len == 0 {
            return TestResult::discard();
        }
        let mut instance = Instance::default();
        let var = Variable::temp(Sort::String);
        instance.add_var(var.clone());
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = SubstitutionEncoder::new(alphabet.clone());
        encoder.singular = true;
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds.clone(), true);
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode(&bounds, &mut encoding, &instance) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = get_substitutions(&encoding, &instance, &solver);
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
        let mut instance = Instance::default();
        let var = Variable::temp(Sort::String);
        instance.add_var(var.clone());
        let alphabet = IndexSet::from_iter(vec!['a', 'b', 'c', 'd']);

        let mut encoder = SubstitutionEncoder::new(alphabet.clone());
        let bounds = Bounds::with_defaults(IntDomain::Bounded(0, len as isize));
        let mut encoding = DomainEncoding::new(alphabet, bounds, false);
        let mut solver: cadical::Solver = cadical::Solver::new();
        match encoder.encode(&encoding.bounds.clone(), &mut encoding, &instance) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }
        encoding.bounds.double_uppers();
        match encoder.encode(&encoding.bounds.clone(), &mut encoding, &instance) {
            crate::encode::EncodingResult::Cnf(cnf, _) => {
                cnf.into_iter().for_each(|cl| solver.add_clause(cl));
                solver.solve();
            }
            crate::encode::EncodingResult::Trivial(_) => unreachable!(),
        }

        // This will panic if the substitution is not valid
        let subs = get_substitutions(&encoding, &instance, &solver);
        assert!(
            subs.get(&var).is_some(),
            "No substitution found (length is {}) {:?}",
            len,
            subs
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
