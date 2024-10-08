use std::fmt::{self, Display, Formatter};

use indexmap::IndexSet;

use crate::{
    context::Sorted,
    ir::{util::partition_by_vars, AtomType, Formula, Literal},
};

use regulaer::alph::Alphabet as InnerAlphabet;

/// A wrapper around the regular crate's alphabet
#[derive(Debug, Clone, Default)]
pub struct Alphabet(InnerAlphabet);

impl Alphabet {
    /// Returns an iterator over the characters in the alphabet
    pub fn iter(&self) -> impl Iterator<Item = char> + '_ {
        self.0.iter_chars()
    }

    #[allow(dead_code)]
    pub fn insert_char(&mut self, c: char) {
        self.0.insert_char(c);
    }
}

impl FromIterator<char> for Alphabet {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut alph = InnerAlphabet::default();
        for c in iter {
            alph.insert_char(c);
        }
        Alphabet(alph)
    }
}
impl From<InnerAlphabet> for Alphabet {
    fn from(alph: InnerAlphabet) -> Self {
        Alphabet(alph)
    }
}

impl Display for Alphabet {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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

    Alphabet(inferred_alphabet)
}

const SMT_MAX_CHAR: u32 = 0x2FFFF;
/// Returns the alphabet of constants in the formula.
/// The alphabet is not canonicalized.
fn alphabet_of(fm: &Formula) -> InnerAlphabet {
    let mut alph = InnerAlphabet::default();
    for l in fm.literals() {
        for c in l.constants() {
            if c as u32 <= SMT_MAX_CHAR {
                alph.insert_char(c);
            }
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
        match lit.atom().get_type() {
            AtomType::BoolVar(_) => (),
            AtomType::InRe(in_re) => {
                string_vars.extend(in_re.variables());
                at_least_one = true;
            }
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
            AtomType::LinearConstraint(lc) => {
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
    use std::rc::Rc;

    use super::*;
    use crate::{
        context::{Context, Sort},
        ir::{
            Atom, LinearArithTerm, LinearOperator, LinearSummand, Literal, Pattern, WordEquation,
        },
    };

    fn make_in_re(var: &str, ctx: &mut Context) -> Rc<Atom> {
        let x = ctx.make_var(var.to_string(), Sort::String).unwrap();
        let re = ctx.re_builder().word("foo".into());
        ctx.ir_builder().in_re(Pattern::variable(x.as_ref()), re)
    }

    fn make_neq(lvar: &str, rvar: &str, ctx: &mut Context) -> Literal {
        let x = ctx.make_var(lvar.to_string(), Sort::String).unwrap();
        let y = ctx.make_var(rvar.to_string(), Sort::String).unwrap();
        let weq = WordEquation::VarEquality(x.as_ref().clone(), y.as_ref().clone());
        let atom = ctx.ir_builder().register_atom(AtomType::WordEquation(weq));
        Literal::Negative(atom)
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
        let mut ctx = Context::default();

        let inre = make_in_re("x", &mut ctx);

        let lit = Literal::Positive(inre.clone());
        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_chars_single_in_re_neq() {
        let mut ctx = Context::default();

        let inre = make_in_re("x", &mut ctx);
        let neq = make_neq("x", "y", &mut ctx);

        let lit = Literal::Positive(inre.clone());
        let result = addition_chars_lits(&[lit, neq]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_chars_single_neqs_more_vars() {
        let mut ctx = Context::default();

        let neq = make_neq("x", "y", &mut ctx);
        let neq_2 = make_neq("y", "z", &mut ctx);
        let neq_3 = make_neq("z", "u", &mut ctx);
        let result = addition_chars_lits(&[neq, neq_2, neq_3]);
        assert_eq!(result, 3); // 4 vars, 3 inequalities => 3 additional characters
    }

    #[test]
    fn test_addition_chars_single_in_re_neq_more_ineqs() {
        let mut ctx = Context::default();

        let neq_xy = make_neq("x", "y", &mut ctx);
        let neq_xz = make_neq("x", "z", &mut ctx);
        let neq_xu = make_neq("x", "u", &mut ctx);

        let neq_yz = make_neq("y", "z", &mut ctx);
        let neq_yu = make_neq("y", "u", &mut ctx);

        let neq_zu = make_neq("z", "u", &mut ctx);

        let result = addition_chars_lits(&[neq_xy, neq_xz, neq_xu, neq_yz, neq_yu, neq_zu]);
        assert_eq!(result, 4); // 4 vars, 6 inequalities => 4 additional characters
    }

    #[test]
    fn test_addition_lc_wo_string() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::Int).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::Int).unwrap();

        let mut lhs = LinearArithTerm::new();
        lhs.add_summand(LinearSummand::int_variable(x.as_ref().clone(), 5));
        lhs.add_summand(LinearSummand::int_variable(y.as_ref().clone(), 3));
        lhs.add_summand(LinearSummand::constant(2));

        let rhs = 10;
        let lc = ctx
            .ir_builder()
            .linear_constraint(lhs, LinearOperator::Eq, rhs);
        let lit = Literal::Positive(lc);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_addition_lc_w_string() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::Int).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();

        let mut lhs = LinearArithTerm::new();
        lhs.add_summand(LinearSummand::int_variable(x.as_ref().clone(), 5));
        lhs.add_summand(LinearSummand::len_variable(y.as_ref().clone(), 3));
        lhs.add_summand(LinearSummand::constant(2));

        let rhs = 10;
        let lc = ctx
            .ir_builder()
            .linear_constraint(lhs, LinearOperator::Eq, rhs);
        let lit = Literal::Positive(lc);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();

        let mut lhs = LinearArithTerm::new();
        lhs.add_summand(LinearSummand::len_variable(x.as_ref().clone(), 5));
        lhs.add_summand(LinearSummand::len_variable(y.as_ref().clone(), 3));
        lhs.add_summand(LinearSummand::constant(2));

        let rhs = 10;
        let lc = ctx
            .ir_builder()
            .linear_constraint(lhs, LinearOperator::Eq, rhs);
        let lit = Literal::Positive(lc);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings_with_neq() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();

        let mut lhs = LinearArithTerm::new();
        lhs.add_summand(LinearSummand::len_variable(x.as_ref().clone(), 5));
        lhs.add_summand(LinearSummand::len_variable(y.as_ref().clone(), 3));
        lhs.add_summand(LinearSummand::constant(2));

        let rhs = 10;
        let lc = ctx
            .ir_builder()
            .linear_constraint(lhs, LinearOperator::Eq, rhs);
        let lit = Literal::Positive(lc);

        let neq = make_neq("x", "y", &mut ctx);

        let result = addition_chars_lits(&[lit, neq]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_three_strings_with_neq() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();

        let mut lhs = LinearArithTerm::new();
        lhs.add_summand(LinearSummand::len_variable(x.as_ref().clone(), 5));
        lhs.add_summand(LinearSummand::len_variable(y.as_ref().clone(), 3));
        lhs.add_summand(LinearSummand::constant(2));

        let rhs = 10;
        let lc = ctx
            .ir_builder()
            .linear_constraint(lhs, LinearOperator::Eq, rhs);
        let lit = Literal::Positive(lc);

        let neq = make_neq("x", "y", &mut ctx);
        let neq_2 = make_neq("y", "z", &mut ctx);

        let result = addition_chars_lits(&[lit, neq, neq_2]);
        assert_eq!(result, 2);
    }

    #[test]
    #[ignore = "Implement me"]
    fn test_addition_chars_lits_weq() {}

    #[test]
    #[ignore = "Implement me"]
    fn test_addition_chars_lits_weq_reg() {}

    #[test]
    #[ignore = "Implement me"]
    fn test_addition_chars_reg_lin() {}
}
