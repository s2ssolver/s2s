use std::collections::HashMap;

use indexmap::{IndexMap, IndexSet};

use crate::{
    ast::{Sort, Variable},
    bounds::Bounds,
    encode::LAMBDA,
    instance::Instance,
    sat::{as_lit, PLit, PVar},
};

pub struct DomainEncoding {
    /// The encoding of the substitutions
    pub(super) string: SubstitutionEncoding,
    /// The encoding of the integer domains
    pub(super) int: IntEncoding,

    /// The alphabet used for the substitutions
    alphabet: IndexSet<char>,
    /// If true, then no lambda substitutions are allowed
    singular: bool,
    /// The bounds of the integer variables
    pub(super) bounds: Bounds,
}

/// Propositional encoding of the domains of all variables.

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

    pub fn is_singular(&self) -> bool {
        self.singular
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

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, isize, &PVar)> {
        self.encodings
            .iter()
            .map(|((var, value), v)| (var, *value, v))
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

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, usize, char, &PVar)> {
        self.encodings
            .iter()
            .map(|((var, pos, chr), v)| (var, *pos, *chr, v))
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

    pub(super) fn add(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.encodings.insert((var.clone(), pos, chr), v);
    }
}

/// Reads the substitutions from the model.
/// Panics if the solver is not in a SAT state.
/// TODO: Move this into the SubstitutionEncoding struct
pub fn get_str_substitutions(
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
    for (var, pos, chr, v) in domain_encoding.string().iter() {
        if let Some(true) = solver.value(as_lit(*v)) {
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
}

/// Reads the integer substitutions from the model.
/// Panics if the solver is not in a SAT state.
/// TODO: Move this into the SubstitutionEncoding struct
pub fn get_int_substitutions(
    domain_encoding: &DomainEncoding,
    solver: &cadical::Solver,
) -> HashMap<Variable, isize> {
    if solver.status() != Some(true) {
        panic!("Solver is not in a SAT state")
    }
    let mut subs = HashMap::new();
    for (var, l, v) in domain_encoding.int().iter() {
        if let Some(true) = solver.value(as_lit(*v)) {
            let ok = subs.insert(var.clone(), l);
            assert!(ok.is_none());
        }
    }

    subs
}
