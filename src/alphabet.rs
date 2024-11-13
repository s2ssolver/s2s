use std::{
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use indexmap::IndexSet;

use crate::{
    canonical::{util::partition_by_vars, AtomKind, Formula, Literal},
    context::Sorted,
};

use regulaer::{alph::Alphabet as InnerAlphabet, re::RegexProps};

/// A wrapper around the regular crate's alphabet
#[derive(Debug, Clone, Default)]
pub struct Alphabet {
    inner: Rc<InnerAlphabet>,
    size: usize,
}

impl Alphabet {
    fn new(inner: Rc<InnerAlphabet>) -> Self {
        let size = inner.iter_chars().count();
        Alphabet { inner, size }
    }
    /// Returns an iterator over the characters in the alphabet
    pub fn iter(&self) -> impl Iterator<Item = char> + '_ {
        self.inner.iter_chars()
    }

    /// Returns the number of characters in the alphabet
    pub fn len(&self) -> usize {
        self.size
    }
}

impl FromIterator<char> for Alphabet {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut alph = InnerAlphabet::default();
        for c in iter {
            alph.insert_char(c);
        }
        Alphabet::new(Rc::new(alph))
    }
}
impl From<InnerAlphabet> for Alphabet {
    fn from(alph: InnerAlphabet) -> Self {
        Alphabet::new(Rc::new(alph))
    }
}

impl Display for Alphabet {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

/// Infers the alphabet needed to solve the formula.
/// Returns an [Alphabet] that is large enough such that if the formula is satisfiable
/// in any super-alphabet of the inferred alphabet, then it is satisfiable in the inferred alphabet.
/// The formula must be in normal form.
pub fn infer(fm: &Formula) -> Alphabet {
    let mut inferred_alphabet = alphabet_of(fm);
    let complement_alphabet = inferred_alphabet.complement();
    let num_additional_chars = additional_chars(fm);

    complement_alphabet
        .iter_chars()
        .take(num_additional_chars)
        .for_each(|c| {
            inferred_alphabet.insert_char(c);
        });

    if inferred_alphabet
        .iter_ranges()
        .filter(|r| !r.is_empty())
        .count()
        == 0
    {
        inferred_alphabet.insert_char('a');
    }

    inferred_alphabet.canonicalize();

    Alphabet::new(Rc::new(inferred_alphabet))
}

const SMT_MAX_CHAR: u32 = 0x2FFFF;
/// Returns the alphabet of constants in the formula.
/// The alphabet is not canonicalized.
fn alphabet_of(fm: &Formula) -> InnerAlphabet {
    let mut alph = InnerAlphabet::default();
    for l in fm.literals() {
        for c in constants_of(&l) {
            if c as u32 <= SMT_MAX_CHAR {
                alph.insert_char(c);
            }
        }
    }

    alph
}

fn constants_of(lit: &Literal) -> IndexSet<char> {
    let atom = lit.atom();
    match atom.kind() {
        crate::canonical::AtomKind::Boolvar(_) => IndexSet::new(),
        crate::canonical::AtomKind::WordEquation(weq) => weq.constants(),
        crate::canonical::AtomKind::InRe(inre) => inre.re().alphabet().iter_chars().collect(),
        crate::canonical::AtomKind::FactorConstraint(rfc) => rfc.rhs().chars().collect(),
        crate::canonical::AtomKind::Linear(_) => IndexSet::new(),
    }
}

/// Returns the number of additional characters we need to the alphabet in order to stay equisatisfiable.
fn additional_chars(fm: &Formula) -> usize {
    // Partition the literals based on variable dependencies

    // Cloning is cheap, because all atoms are reference counted pointers
    let lits = Vec::from_iter(fm.literals().into_iter());
    let parts = partition_by_vars(&lits);

    // For each partition, compute the number of characters needed to encode the partition and take the maximum
    // If no partitions are present, or no partition requires additional characters, return 0
    parts
        .iter()
        .map(|part| addition_chars_lits(part))
        .max()
        .unwrap_or(0)
}

/// Returns the number of additional characters needed for the given set of literals.
/// If the literals do not contain (proper) word equations, then the number of additional characters is min(#string vars, #string inequalities).
/// If the literals contain word equations, then the number of additional characters is #string inequalities.
/// Addtionally, if the the literals contain at least one linear constraint or one regular constraint, then the number of additional characters is at least 1.
fn addition_chars_lits(lits: &[Literal]) -> usize {
    let mut contains_eq = false;

    let mut string_vars = IndexSet::new();
    let mut num_ineqs = 0;
    let mut at_least_one = false;

    for lit in lits {
        let pol = lit.polarity();
        match lit.atom().kind() {
            AtomKind::Boolvar(_) => (),
            AtomKind::InRe(in_re) => {
                string_vars.insert(in_re.lhs().clone());
                at_least_one = true;
            }
            AtomKind::WordEquation(weq) => {
                string_vars.extend(weq.variables());
                contains_eq |= weq.is_proper();
                if !pol {
                    num_ineqs += 1;
                }
            }
            AtomKind::FactorConstraint(fc) => {
                string_vars.insert(fc.lhs().clone());
                at_least_one = true;
            }
            AtomKind::Linear(lc) => {
                // Can contain string vars, but if they don't occur in the other literals, we need at most one character to account for all possible lengths
                if lc.variables().iter().any(|v| v.sort().is_string()) {
                    at_least_one = true;
                }
            }
        }
    }

    let num_vars = string_vars.len();
    let res = if contains_eq {
        num_ineqs
    } else {
        num_vars.min(num_ineqs)
    };
    if at_least_one {
        res.max(1)
    } else {
        res
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{
        canonical::{canonicalize, LinearArithTerm, LinearSummand},
        context::Sort,
        node::{Node, NodeManager},
    };

    fn to_lit(node: &Node, mngr: &mut NodeManager) -> Literal {
        match canonicalize(node, mngr).unwrap().kind() {
            crate::canonical::FormulaKind::Literal(literal) => literal.clone(),
            _ => unreachable!(),
        }
    }

    fn make_in_re(var: &str, mngr: &mut NodeManager) -> Literal {
        let x = mngr
            .new_var(var.to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .unwrap();
        let re = mngr.re_builder().word("foo".into());
        let re = mngr.const_regex(re);
        let inre = mngr.in_re(x, re);
        to_lit(&inre, mngr)
    }

    fn make_neq(lvar: &str, rvar: &str, mngr: &mut NodeManager) -> Literal {
        let x = mngr.new_var(lvar.to_string(), Sort::String).unwrap();
        let y = mngr.new_var(rvar.to_string(), Sort::String).unwrap();
        let x = mngr.var(x);
        let y = mngr.var(y);
        let eq = mngr.eq(x, y);
        let neq = mngr.not(eq);
        to_lit(&neq, mngr)
    }

    #[test]
    fn test_addition_chars_lits_empty() {
        let literals = vec![];
        let result = addition_chars_lits(&literals);
        assert_eq!(
            result, 0,
            "Expected 0 additional characters for an empty literal set"
        );
    }

    #[test]
    fn test_addition_chars_single_in_re_only() {
        let mut mngr = NodeManager::default();

        let inre = make_in_re("x", &mut mngr);

        let result = addition_chars_lits(&[inre]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_chars_single_in_re_neq() {
        let mut mngr = NodeManager::default();

        let inre = make_in_re("x", &mut mngr);
        let neq = make_neq("x", "y", &mut mngr);
        let result = addition_chars_lits(&[inre, neq]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_chars_single_neqs_more_vars() {
        let mut mngr = NodeManager::default();

        let neq = make_neq("x", "y", &mut mngr);
        let neq_2 = make_neq("y", "z", &mut mngr);
        let neq_3 = make_neq("z", "u", &mut mngr);
        let result = addition_chars_lits(&[neq, neq_2, neq_3]);
        assert_eq!(result, 3); // 4 vars, 3 inequalities => 3 additional characters
    }

    #[test]
    fn test_addition_chars_single_in_re_neq_more_ineqs() {
        let mut mngr = NodeManager::default();

        let neq_xy = make_neq("x", "y", &mut mngr);
        let neq_xz = make_neq("x", "z", &mut mngr);
        let neq_xu = make_neq("x", "u", &mut mngr);

        let neq_yz = make_neq("y", "z", &mut mngr);
        let neq_yu = make_neq("y", "u", &mut mngr);

        let neq_zu = make_neq("z", "u", &mut mngr);

        let result = addition_chars_lits(&[neq_xy, neq_xz, neq_xu, neq_yz, neq_yu, neq_zu]);
        assert_eq!(result, 4); // 4 vars, 6 inequalities => 4 additional characters
    }

    #[test]
    fn test_addition_lc_wo_string() {
        let mut mngr = NodeManager::default();
        let x = mngr
            .new_var("x".to_string(), Sort::Int)
            .map(|v| mngr.var(v))
            .unwrap();
        let y = mngr
            .new_var("y".to_string(), Sort::Int)
            .map(|v| mngr.var(v))
            .unwrap();

        let const_5 = mngr.const_int(5);
        let const_3 = mngr.const_int(3);
        let const_2 = mngr.const_int(2);

        let s1 = mngr.mul(vec![x.clone(), const_5]);
        let s2 = mngr.mul(vec![y.clone(), const_3]);
        let s3 = mngr.mul(vec![const_2]);

        let lhs = mngr.add(vec![s1, s2, s3]);

        let rhs = mngr.const_int(10);
        let lc = mngr.eq(lhs, rhs);

        let lit = to_lit(&lc, &mut mngr);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_addition_lc_w_string() {
        let mut mngr = NodeManager::default();
        let x_len = mngr
            .new_var("x".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();
        let y = mngr
            .new_var("y".to_string(), Sort::Int)
            .map(|v| mngr.var(v))
            .unwrap();

        let const_5 = mngr.const_int(5);
        let const_3 = mngr.const_int(3);
        let const_2 = mngr.const_int(2);

        let s1 = mngr.mul(vec![x_len.clone(), const_5]);
        let s2 = mngr.mul(vec![y.clone(), const_3]);
        let s3 = mngr.mul(vec![const_2]);

        let lhs = mngr.add(vec![s1, s2, s3]);

        let rhs = mngr.const_int(10);
        let lc = mngr.eq(lhs, rhs);

        let lit = to_lit(&lc, &mut mngr);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings() {
        let mut mngr = NodeManager::default();
        let x_len = mngr
            .new_var("x".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();
        let y_len = mngr
            .new_var("y".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();

        let const_5 = mngr.const_int(5);
        let const_3 = mngr.const_int(3);
        let const_2 = mngr.const_int(2);

        let s1 = mngr.mul(vec![x_len.clone(), const_5]);
        let s2 = mngr.mul(vec![y_len.clone(), const_3]);
        let s3 = mngr.mul(vec![const_2]);

        let lhs = mngr.add(vec![s1, s2, s3]);

        let rhs = mngr.const_int(10);
        let lc = mngr.eq(lhs, rhs);

        let lit = to_lit(&lc, &mut mngr);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings_with_neq() {
        let mut mngr = NodeManager::default();
        let x_len = mngr
            .new_var("x".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();
        let y_len = mngr
            .new_var("y".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();

        let const_5 = mngr.const_int(5);
        let const_3 = mngr.const_int(3);
        let const_2 = mngr.const_int(2);

        let s1 = mngr.mul(vec![x_len.clone(), const_5]);
        let s2 = mngr.mul(vec![y_len.clone(), const_3]);
        let s3 = mngr.mul(vec![const_2]);

        let lhs = mngr.add(vec![s1, s2, s3]);

        let rhs = mngr.const_int(10);
        let lc = mngr.eq(lhs, rhs);

        let lit = to_lit(&lc, &mut mngr);

        let neq = make_neq("x", "y", &mut mngr);

        let result = addition_chars_lits(&[lit, neq]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_three_strings_with_neq() {
        let mut mngr = NodeManager::default();
        let x_len = mngr
            .new_var("x".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();
        let y_len = mngr
            .new_var("y".to_string(), Sort::String)
            .map(|v| mngr.var(v))
            .map(|v| mngr.str_len(v))
            .unwrap();

        let const_5 = mngr.const_int(5);
        let const_3 = mngr.const_int(3);
        let const_2 = mngr.const_int(2);

        let s1 = mngr.mul(vec![x_len.clone(), const_5]);
        let s2 = mngr.mul(vec![y_len.clone(), const_3]);
        let s3 = mngr.mul(vec![const_2]);

        let lhs = mngr.add(vec![s1, s2, s3]);

        let rhs = mngr.const_int(10);
        let lc = mngr.eq(lhs, rhs);

        let lit = to_lit(&lc, &mut mngr);

        let neq = make_neq("x", "y", &mut mngr);
        let neq_2 = make_neq("y", "z", &mut mngr);

        let result = addition_chars_lits(&[lit, neq, neq_2]);
        assert_eq!(result, 2);
    }
}
