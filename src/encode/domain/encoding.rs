use std::{collections::HashMap, rc::Rc};

use indexmap::IndexMap;

use crate::{
    alphabet::Alphabet,
    bounds::Bounds,
    context::Context,
    encode::LAMBDA,
    repr::{Sort, Sorted, Variable},
    sat::{plit, PLit, PVar},
};

#[derive(Clone, Debug)]
pub struct DomainEncoding {
    /// The encoding of the substitutions
    pub(super) string: StringDomain,
    /// The encoding of the integer domains
    pub(super) int: IntDomain,

    /// The alphabet used for the substitutions
    alphabet: Alphabet,

    /// The bounds of the integer variables
    pub(super) bounds: Bounds,
}

/// Propositional encoding of the domains of all variables.

impl DomainEncoding {
    pub fn new(alphabet: Alphabet, bounds: Bounds) -> Self {
        Self {
            string: StringDomain::new(),
            int: IntDomain::default(),
            alphabet,
            bounds,
        }
    }

    pub fn string(&self) -> &StringDomain {
        &self.string
    }

    pub fn int(&self) -> &IntDomain {
        &self.int
    }

    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    pub fn alphabet_lambda(&self) -> Alphabet {
        let mut alph = self.alphabet.clone();
        alph.insert_char(LAMBDA);
        alph
    }
}

#[derive(Clone, Debug, Default)]
pub struct IntDomain {
    encodings: IndexMap<(Variable, isize), PVar>,
}

impl IntDomain {
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
pub struct StringDomain {
    substitutions: HashMap<(Variable, usize, char), PVar>,
    lengths: IndexMap<(Variable, usize), PVar>,
}

impl StringDomain {
    pub fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
            lengths: IndexMap::new(),
        }
    }

    pub fn iter_substitutions(&self) -> impl Iterator<Item = (&Variable, usize, char, &PVar)> {
        self.substitutions
            .iter()
            .map(|((var, pos, chr), v)| (var, *pos, *chr, v))
    }

    pub fn get_sub(&self, var: &Variable, pos: usize, chr: char) -> Option<PVar> {
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

    pub(super) fn get_sub_lit(&self, var: &Variable, pos: usize, chr: char) -> Option<PLit> {
        self.get_sub(var, pos, chr).map(plit)
    }

    pub(super) fn inser_substitution(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );

        self.substitutions.insert((var.clone(), pos, chr), v);
    }

    pub(super) fn inser_lenght(&mut self, var: &Variable, len: usize, v: PVar) {
        assert!(
            var.sort() == Sort::String,
            "Variable {} is not a string",
            var
        );
        let ok = self.lengths.insert((var.clone(), len), v);
        assert!(ok.is_none());
    }
}

/// Reads the substitutions from the model.
/// Panics if the solver is not in a SAT state.
/// TODO: Move this into the SubstitutionEncoding struct
pub fn get_str_substitutions(
    domain_encoding: &DomainEncoding,
    ctx: &Context,
    solver: &cadical::Solver,
) -> HashMap<Rc<Variable>, Vec<char>> {
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
                    .get_upper(str_var)
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
        if let Some(true) = solver.value(plit(*v)) {
            let ok = subs.insert(var.clone(), l);
            assert!(ok.is_none());
        }
    }

    subs
}
