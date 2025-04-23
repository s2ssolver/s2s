use std::rc::Rc;

use indexmap::IndexSet;
use smt_str::SmtChar;

use crate::{
    ast::{
        canonical::{util::partition_by_vars, AtomKind, Literal},
        get_literals, Node,
    },
    context::Sorted,
};

pub use smt_str::alphabet::Alphabet;

/// Infers the alphabet needed to solve the formula.
/// Returns an [Alphabet] that is large enough such that if the formula is satisfiable
/// in any super-alphabet of the inferred alphabet, then it is satisfiable in the inferred alphabet.
/// The formula must be in normal form.
pub fn infer(fm: &Node) -> Rc<Alphabet> {
    let mut inferred_alphabet = alphabet_of(fm);
    let complement_alphabet = inferred_alphabet.complement();
    let num_additional_chars = additional_chars(fm);

    complement_alphabet
        .iter()
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

    Rc::new(inferred_alphabet)
}

/// Returns the alphabet of constants in the formula.
/// The alphabet is not canonicalized.
fn alphabet_of(fm: &Node) -> Alphabet {
    let mut alph = Alphabet::default();
    for l in get_literals(fm) {
        for c in constants_of(&l) {
            alph.insert_char(c);
        }
    }

    alph
}

fn constants_of(lit: &Literal) -> IndexSet<SmtChar> {
    let atom = lit.atom();
    match atom.kind() {
        AtomKind::Boolvar(_) => IndexSet::new(),
        AtomKind::WordEquation(weq) => weq.constants(),
        AtomKind::InRe(inre) => inre.re().alphabet().iter().collect(),
        AtomKind::FactorConstraint(rfc) => rfc.rhs().iter().copied().collect(),
        AtomKind::Linear(_) => IndexSet::new(),
    }
}

/// Returns the number of additional characters we need to the alphabet in order to stay equisatisfiable.
fn additional_chars(fm: &Node) -> usize {
    // Partition the literals based on variable dependencies

    // Cloning is cheap, because all atoms are reference counted pointers
    let lits = Vec::from_iter(get_literals(fm));
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
/// If the literals contain length a constraints, then another character is needed on top of the above.
/// Always returns at least 1.
fn addition_chars_lits(lits: &[Literal]) -> usize {
    let mut contains_eq = false;
    let mut contains_lc = false;
    let mut contains_inre = false;

    let mut string_vars = IndexSet::new();
    let mut num_ineqs = 0;

    for lit in lits {
        let pol = lit.polarity();
        match lit.atom().kind() {
            AtomKind::Boolvar(_) => (),
            AtomKind::InRe(in_re) => {
                string_vars.insert(in_re.lhs().clone());
                contains_inre = true;
            }
            AtomKind::WordEquation(weq) => {
                string_vars.extend(weq.variables());
                contains_eq |= weq.is_proper();
                if !pol {
                    num_ineqs += 1;
                }
            }
            AtomKind::FactorConstraint(fc) => {
                string_vars.insert(fc.of().clone());
                contains_inre = true;
            }
            AtomKind::Linear(lc) => {
                // Can contain string vars, but if they don't occur in the other literals, we need at most one character to account for all possible lengths
                if lc.variables().iter().any(|v| v.sort().is_string()) {
                    contains_lc = true;
                }
            }
        }
    }

    let num_vars = string_vars.len();

    // If the formula contains a word equation, then we need at least the number of inequalities + 1 characters
    // If the formula does not contain a word equation, then we need at least the minimum of the number of string variables and the number of inequalities + 1 characters
    // TODO: By Diekert we can improve number of inequalities + 1 to (1/2 + sqrt(2*(number of ineqs)+1/2))
    let res = match (contains_inre, contains_eq) {
        (true, true) => num_ineqs + 1,
        (true, false) => num_vars.min(num_ineqs + 1),
        (false, true) => num_ineqs + 1,
        (false, false) => num_vars.min(num_ineqs + 1),
    };
    // If the formula contains a linear constraint with string variables, the we need at least one character
    // here are some minimal example
    // - x != y /\ |x| = |y| (needs at least 2 characters, satisifed because we are regular and have two string vars)
    // - xx != yy /\ |xx| = |yy| (needs at least 2 characters, because we concatenation and an inequality)

    if contains_lc {
        res.max(1)
    } else {
        res
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{
        ast::{Node, NodeKind},
        context::{Context, Sort},
        preprocess::canonicalize,
    };

    fn to_lit(node: &Node, ctx: &mut Context) -> Literal {
        match canonicalize(node, ctx).kind() {
            NodeKind::Literal(literal) => literal.clone(),
            _ => unreachable!(),
        }
    }

    fn make_in_re(var: &str, ctx: &mut Context) -> Literal {
        let x = ctx
            .new_var(var.to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .unwrap();
        let re = ctx.re_builder().to_re("foo".into());
        let re = ctx.ast().const_regex(re);
        let inre = ctx.ast().in_re(x, re);
        to_lit(&inre, ctx)
    }

    fn make_neq(lvar: &str, rvar: &str, ctx: &mut Context) -> Literal {
        let x = ctx.new_var(lvar.to_string(), Sort::String).unwrap();
        let y = ctx.new_var(rvar.to_string(), Sort::String).unwrap();
        let x = ctx.ast().variable(x);
        let y = ctx.ast().variable(y);
        let eq = ctx.ast().eq(x, y);
        let neq = ctx.ast().not(eq);
        to_lit(&neq, ctx)
    }

    #[test]
    fn test_addition_chars_lits_empty() {
        let literals = vec![];
        let result = addition_chars_lits(&literals);
        assert_eq!(
            result, 0,
            "Expected 1 additional characters for an empty literal set"
        );
    }

    #[test]
    fn test_addition_chars_single_in_re_only() {
        let mut ctx = Context::default();

        let inre = make_in_re("x", &mut ctx);

        let result = addition_chars_lits(&[inre]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_chars_single_in_re_neq() {
        // x in foo /\ x != y
        let mut ctx = Context::default();
        let inre = make_in_re("x", &mut ctx);
        let neq = make_neq("x", "y", &mut ctx);
        let result = addition_chars_lits(&[inre, neq]);
        assert_eq!(result, 2); // 2 string vars, 1 inequality, no concat => min(2, 1+1) = 2 additional characters
    }

    #[test]
    fn test_addition_chars_single_neqs_more_vars() {
        // x != y /\ x != z /\ x != u
        let mut ctx = Context::default();

        let neq = make_neq("x", "y", &mut ctx);
        let neq_2 = make_neq("y", "z", &mut ctx);
        let neq_3 = make_neq("z", "u", &mut ctx);
        let result = addition_chars_lits(&[neq, neq_2, neq_3]);
        assert_eq!(result, 4); // 4 vars, 3 inequalities => min(4, 3+1) = 4 additional characters
    }

    #[test]
    fn test_addition_chars_only_neqs() {
        // x!=y /\ x != z /\ x != u /\ y != z /\ y != u /\ z != u
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
        // x * 5 + y * 3 + 2 = 10
        let mut ctx = Context::default();
        let x = ctx
            .new_var("x".to_string(), Sort::Int)
            .map(|v| ctx.ast().variable(v))
            .unwrap();
        let y = ctx
            .new_var("y".to_string(), Sort::Int)
            .map(|v| ctx.ast().variable(v))
            .unwrap();

        let const_5 = ctx.ast().const_int(5);
        let const_3 = ctx.ast().const_int(3);
        let const_2 = ctx.ast().const_int(2);

        let s1 = ctx.ast().mul(vec![x.clone(), const_5]);
        let s2 = ctx.ast().mul(vec![y.clone(), const_3]);
        let s3 = ctx.ast().mul(vec![const_2]);

        let lhs = ctx.ast().add(vec![s1, s2, s3]);

        let rhs = ctx.ast().const_int(10);
        let lc = ctx.ast().eq(lhs, rhs);

        let lit = to_lit(&lc, &mut ctx);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 0); // only LC without string vars, no additional characters needed
    }

    #[test]
    fn test_addition_lc_w_string() {
        let mut ctx = Context::default();
        let x_len = ctx
            .new_var("x".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();
        let y = ctx
            .new_var("y".to_string(), Sort::Int)
            .map(|v| ctx.ast().variable(v))
            .unwrap();

        let const_5 = ctx.ast().const_int(5);
        let const_3 = ctx.ast().const_int(3);
        let const_2 = ctx.ast().const_int(2);

        let s1 = ctx.ast().mul(vec![x_len.clone(), const_5]);
        let s2 = ctx.ast().mul(vec![y.clone(), const_3]);
        let s3 = ctx.ast().mul(vec![const_2]);

        let lhs = ctx.ast().add(vec![s1, s2, s3]);

        let rhs = ctx.ast().const_int(10);
        let lc = ctx.ast().eq(lhs, rhs);

        let lit = to_lit(&lc, &mut ctx);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings() {
        let mut ctx = Context::default();
        let x_len = ctx
            .new_var("x".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();
        let y_len = ctx
            .new_var("y".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();

        let const_5 = ctx.ast().const_int(5);
        let const_3 = ctx.ast().const_int(3);
        let const_2 = ctx.ast().const_int(2);

        let s1 = ctx.ast().mul(vec![x_len.clone(), const_5]);
        let s2 = ctx.ast().mul(vec![y_len.clone(), const_3]);
        let s3 = ctx.ast().mul(vec![const_2]);

        let lhs = ctx.ast().add(vec![s1, s2, s3]);

        let rhs = ctx.ast().const_int(10);
        let lc = ctx.ast().eq(lhs, rhs);

        let lit = to_lit(&lc, &mut ctx);

        let result = addition_chars_lits(&[lit]);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_addition_lc_two_strings_with_neq() {
        // x * 5 + y * 3 + 2 = 10 /\ x != y

        let mut ctx = Context::default();
        let x_len = ctx
            .new_var("x".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();
        let y_len = ctx
            .new_var("y".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();

        let const_5 = ctx.ast().const_int(5);
        let const_3 = ctx.ast().const_int(3);
        let const_2 = ctx.ast().const_int(2);

        let s1 = ctx.ast().mul(vec![x_len.clone(), const_5]);
        let s2 = ctx.ast().mul(vec![y_len.clone(), const_3]);
        let s3 = ctx.ast().mul(vec![const_2]);

        let lhs = ctx.ast().add(vec![s1, s2, s3]);

        let rhs = ctx.ast().const_int(10);
        let lc = ctx.ast().eq(lhs, rhs);

        let lit = to_lit(&lc, &mut ctx);

        let neq = make_neq("x", "y", &mut ctx);

        let result = addition_chars_lits(&[lit, neq]);

        assert_eq!(result, 2);
    }

    #[test]
    fn test_addition_lc_three_strings_with_neq() {
        // x * 5 + y * 3 + 2 = 10 /\ x != y /\ y != z
        let mut ctx = Context::default();
        let x_len = ctx
            .new_var("x".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();
        let y_len = ctx
            .new_var("y".to_string(), Sort::String)
            .map(|v| ctx.ast().variable(v))
            .map(|v| ctx.ast().str_len(v))
            .unwrap();

        let const_5 = ctx.ast().const_int(5);
        let const_3 = ctx.ast().const_int(3);
        let const_2 = ctx.ast().const_int(2);

        let s1 = ctx.ast().mul(vec![x_len.clone(), const_5]);
        let s2 = ctx.ast().mul(vec![y_len.clone(), const_3]);
        let s3 = ctx.ast().mul(vec![const_2]);

        let lhs = ctx.ast().add(vec![s1, s2, s3]);

        let rhs = ctx.ast().const_int(10);
        let lc = ctx.ast().eq(lhs, rhs);

        let lit = to_lit(&lc, &mut ctx);

        let neq = make_neq("x", "y", &mut ctx);
        let neq_2 = make_neq("y", "z", &mut ctx);

        let result = addition_chars_lits(&[lit, neq, neq_2]);
        assert_eq!(result, 3);
    }
}
