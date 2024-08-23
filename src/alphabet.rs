use indexmap::IndexSet;

use crate::repr::ir::{util::partition_by_vars, AtomType, Formula, Literal};

use regulaer::alph::Alphabet as InnerAlphaber;

/// A wrapper around the regular crate's alphabet
#[derive(Debug, Clone, Default)]
pub struct Alphabet(InnerAlphaber);

impl Alphabet {
    /// Returns an iterator over the characters in the alphabet
    pub fn iter(&self) -> impl Iterator<Item = char> + '_ {
        self.0.iter_chars()
    }

    pub fn insert_char(&mut self, c: char) {
        self.0.insert_char(c);
    }
}

impl FromIterator<char> for Alphabet {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut alph = InnerAlphaber::default();
        for c in iter {
            alph.insert_char(c);
        }
        Alphabet(alph)
    }
}
impl From<InnerAlphaber> for Alphabet {
    fn from(alph: InnerAlphaber) -> Self {
        Alphabet(alph)
    }
}

/// Infers the alphabet needed to solver the formula.
/// Returns an [Alphabet] that is larger enough such that if the formula is satisfiable in any super-alphabet of the inferred alphabet, then it is satisfiable in the inferred alphabet.
/// The formula must be in normal form.
pub fn infer(fm: &Formula) -> Alphabet {
    let mut inner = alphabet_of(fm);

    // The complement, we need it to add the additional characters
    let complement = inner.complement();

    let n = additional_chars(fm); // subtract one because we already added one character

    complement.iter_chars().take(n).for_each(|c| {
        inner.insert_char(c);
    });

    if inner.iter_ranges().filter(|r| !r.is_empty()).count() == 0 {
        // If the alphabet is empty, we need at least one character
        inner.insert_char('a');
    }
    inner.canonicalize();

    Alphabet(inner)
}

/// Returns the alphabet of constants in the formula.
/// The alphabet is not canonicalized.
fn alphabet_of(fm: &Formula) -> InnerAlphaber {
    let mut alph = InnerAlphaber::default();
    for l in fm.literals() {
        for c in l.constants() {
            alph.insert_char(c);
        }
    }

    alph
}

/// Returns the number of additional characters we need to the alphabet in order to stay equisatisfiable.
fn additional_chars(fm: &Formula) -> usize {
    // Partition the literals based on variable dependencies

    // Cloning is cheap, because all atoms are reference counted pointers
    let lits = fm.literals().cloned().collect::<Vec<_>>();
    let parts = partition_by_vars(&lits);

    // For each partition, compute the number of characters needed to encode the partition and take the maximum
    parts
        .iter()
        .map(|part| addition_chars_lits(part))
        .max()
        .unwrap_or(0)
}

/// Returns the number of additional characters needed for the given set of literals.
/// If the literals do not contain (proper) word equations, then the number of additional characters is min(#string vars, #string inequalities).
/// If the literals contain word equations, then the number of additional characters is #string inequalities.
fn addition_chars_lits(lits: &[Literal]) -> usize {
    let mut contains_eq = false;

    let mut string_vars = IndexSet::new();
    let mut num_ineqs = 0;

    for lit in lits {
        let pol = lit.polarity();
        match lit.atom().get_type() {
            AtomType::BoolVar(_) => (),
            AtomType::InRe(in_re) => string_vars.extend(in_re.variables()),
            AtomType::WordEquation(weq) => {
                string_vars.extend(weq.variables());
                contains_eq |= weq.is_proper();
                if !pol {
                    num_ineqs += 1;
                }
            }
            AtomType::PrefixOf(_) | AtomType::SuffixOf(_) | AtomType::Contains(_) => {
                panic!("Not in normal form")
            }
            AtomType::LinearConstraint(_) => todo!(), // Can technically contain string vars, but if they don't occur in the other literals, we need at most one character to account for all possible lengths
        }
    }

    let num_vars = string_vars.len();
    if contains_eq {
        num_ineqs
    } else {
        num_vars.min(num_ineqs)
    }
}
