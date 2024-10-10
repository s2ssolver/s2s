use std::collections::HashMap;

use crate::{
    context::{Context, Variable},
    ir::{
        AtomType, Formula, LinearArithTerm, Literal, Pattern, RegularConstraint, Symbol,
        VarSubstitution, WordEquation,
    },
};

use super::{RewriteSimplifier, Simplifier};

/// We call a regular constraint independent if it has the form `x \in R` where `x` is a variable and `R` is a regular expression and `x` does not occur elsewhere in the formula.
pub struct IndependentVarReducer {
    var_count: HashMap<Variable, usize>,
}

impl IndependentVarReducer {
    pub fn new(fm: &Formula) -> Self {
        let mut var_count = HashMap::new();
        Self::count_vars(fm, &mut var_count);
        Self { var_count }
    }

    fn count_vars(fm: &Formula, count: &mut HashMap<Variable, usize>) {
        match fm {
            Formula::Literal(l) => match l.atom().get_type() {
                AtomType::BoolVar(v) => *count.entry(v.as_ref().clone()).or_default() += 1,
                AtomType::InRe(inre) => Self::count_pattern_vars(inre.pattern(), count),
                AtomType::WordEquation(WordEquation::VarAssignment(x, _)) => {
                    *count.entry(x.clone()).or_default() += 1;
                }
                AtomType::WordEquation(WordEquation::VarEquality(x, y)) => {
                    *count.entry(x.clone()).or_default() += 1;
                    *count.entry(y.clone()).or_default() += 1;
                }
                AtomType::WordEquation(WordEquation::General(l, r)) => {
                    Self::count_pattern_vars(l, count);
                    Self::count_pattern_vars(r, count);
                }
                AtomType::PrefixOf(pr) => {
                    Self::count_pattern_vars(pr.prefix(), count);
                    Self::count_pattern_vars(pr.of(), count);
                }
                AtomType::SuffixOf(suf) => {
                    Self::count_pattern_vars(suf.suffix(), count);
                    Self::count_pattern_vars(suf.of(), count);
                }
                AtomType::Contains(ct) => {
                    Self::count_pattern_vars(ct.needle(), count);
                    Self::count_pattern_vars(ct.haystack(), count);
                }
                AtomType::LinearConstraint(l) => Self::count_linear_vars(l.lhs(), count),
                _ => (),
            },
            Formula::And(fs) | Formula::Or(fs) => {
                fs.iter().for_each(|f| Self::count_vars(f, count));
            }
            _ => (),
        }
    }

    fn count_pattern_vars(pat: &Pattern, count: &mut HashMap<Variable, usize>) {
        for var in pat.iter().filter_map(|s| {
            if let Symbol::Variable(v) = s {
                Some(v)
            } else {
                None
            }
        }) {
            *count.entry(var.clone()).or_default() += 1;
        }
    }

    fn count_linear_vars(t: &LinearArithTerm, count: &mut HashMap<Variable, usize>) {
        for var in t.iter().filter_map(|s| match s {
            crate::ir::LinearSummand::Mult(vt, _) => Some(vt.variable()),
            crate::ir::LinearSummand::Const(_) => None,
        }) {
            *count.entry(var.clone()).or_default() += 1;
        }
    }

    fn is_independent(&self, v: &Variable) -> bool {
        self.var_count.get(v) == Some(&1)
    }

    fn simplify_regular_constraint(
        &self,
        inre: &RegularConstraint,
        pol: bool,
        ctx: &mut Context,
    ) -> Option<VarSubstitution> {
        let pattern = inre.pattern();
        let reg = inre.re();
        // Check if pattern only consists of independet variables
        let mut vars = Vec::new();
        for s in pattern.iter() {
            if let Symbol::Variable(v) = s {
                if !self.is_independent(v) {
                    return None;
                }
                vars.push(v.clone());
            } else {
                return None;
            }
        }

        // All variables are independent, sample a word
        let nfa = if pol {
            ctx.get_nfa(reg)
        } else {
            let builder = ctx.re_builder();
            let comp = builder.comp(reg.clone());
            ctx.get_nfa(&comp)
        };

        let w: String = nfa.sample()?.iter().collect();

        let mut subs = VarSubstitution::empty();
        for (i, v) in vars.iter().enumerate() {
            // set the first to w, the others to empty
            let s = if i == 0 { w.clone() } else { "".to_string() };
            subs.set_str(v.clone(), Pattern::constant(&s));
        }

        Some(subs)
    }
}
impl Simplifier for IndependentVarReducer {
    fn name(&self) -> &'static str {
        "IndependentVarReducer"
    }
}
impl RewriteSimplifier for IndependentVarReducer {
    fn infer(&self, lit: &Literal, _entailed: bool, ctx: &mut Context) -> Option<VarSubstitution> {
        match lit.atom().get_type() {
            AtomType::InRe(inre) => self.simplify_regular_constraint(inre, lit.polarity(), ctx),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use regulaer::{parse::parse_rust_regex, re::Regex};

    use super::*;
    use crate::{
        context::Sort,
        ir::{LinearArithTerm, LinearOperator, LinearSummand, VariableTerm},
    };
    use std::collections::HashMap;

    #[test]
    fn test_counter_pattern_vars_constant() {
        let mut var_count = HashMap::new();
        let pattern = Pattern::constant(&"abc".to_string());
        IndependentVarReducer::count_pattern_vars(&pattern, &mut var_count);
        assert!(var_count.is_empty());
    }

    #[test]
    fn test_counter_pattern_vars_single_var() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let pattern = Pattern::variable(x.as_ref());
        let mut var_count = HashMap::new();

        IndependentVarReducer::count_pattern_vars(&pattern, &mut var_count);
        assert!(var_count.len() == 1);
        assert_eq!(var_count.get(&x), Some(&1));
    }

    #[test]
    fn test_counter_pattern_vars_unique_vars() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();
        let z = ctx.make_var("z".to_string(), Sort::String).unwrap();
        let mut pattern = Pattern::variable(x.as_ref());
        pattern
            .push_var(y.as_ref().clone())
            .push_var(z.as_ref().clone());
        let mut var_count = HashMap::new();

        IndependentVarReducer::count_pattern_vars(&pattern, &mut var_count);
        assert!(var_count.len() == 3);
        assert_eq!(var_count.get(&x), Some(&1));
        assert_eq!(var_count.get(&y), Some(&1));
        assert_eq!(var_count.get(&z), Some(&1));
    }

    #[test]
    fn test_counter_pattern_multiple_var_occurrences() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();
        let z = ctx.make_var("z".to_string(), Sort::String).unwrap();
        let mut pattern = Pattern::variable(x.as_ref());
        pattern
            .push_var(y.as_ref().clone())
            .push_word("foo")
            .push_var(x.as_ref().clone())
            .push_var(z.as_ref().clone())
            .push_word("bar")
            .push_var(y.as_ref().clone());

        let mut var_count = HashMap::new();

        IndependentVarReducer::count_pattern_vars(&pattern, &mut var_count);
        assert!(var_count.len() == 3);
        assert_eq!(var_count.get(&x), Some(&2));
        assert_eq!(var_count.get(&y), Some(&2));
        assert_eq!(var_count.get(&z), Some(&1));
    }

    #[test]
    fn test_count_var_assignment() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let atom = ctx
            .ir_builder()
            .word_equation(Pattern::variable(x.as_ref()), Pattern::constant("foo"));
        let formula = ctx.ir_builder().literal(atom, true);

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert_eq!(var_count.get(&x), Some(&1));
    }

    #[test]
    fn test_count_vars_var_equality_unique() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();
        let atom = ctx
            .ir_builder()
            .word_equation(Pattern::variable(x.as_ref()), Pattern::variable(y.as_ref()));
        let formula = ctx.ir_builder().literal(atom, true);

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert_eq!(var_count.get(&x), Some(&1));
        assert_eq!(var_count.get(&y), Some(&1));
    }

    #[test]
    fn test_count_vars_var_equality_equal() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::String).unwrap();

        let atom = ctx
            .ir_builder()
            .word_equation(Pattern::variable(x.as_ref()), Pattern::variable(x.as_ref()));
        let formula = ctx.ir_builder().literal(atom, true);

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert_eq!(var_count.get(&x), Some(&2));
    }

    #[test]
    fn test_count_vars_with_linear_arith_term() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::Int).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::String).unwrap();

        let mut term = LinearArithTerm::new();
        term.add_summand(LinearSummand::Mult(
            VariableTerm::Int(x.as_ref().clone()),
            1,
        ));
        term.add_summand(LinearSummand::Mult(
            VariableTerm::Len(y.as_ref().clone()),
            1,
        ));

        let atom = ctx
            .ir_builder()
            .linear_constraint(term, LinearOperator::Eq, 2);

        let formula = ctx.ir_builder().literal(atom, true);

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert_eq!(var_count.get(&x), Some(&1));
        assert_eq!(var_count.get(&y), Some(&1));
    }

    #[test]
    fn test_count_vars_with_and_formula() {
        let mut ctx = Context::default();
        let x = ctx.make_var("x".to_string(), Sort::Bool).unwrap();
        let y = ctx.make_var("y".to_string(), Sort::Bool).unwrap();

        let x_var = ctx.ir_builder().bool_var(x.clone());
        let y_var = ctx.ir_builder().bool_var(y.clone());
        let x_lit = ctx.ir_builder().literal(x_var.clone(), true);
        let x_lit2 = ctx.ir_builder().literal(x_var, false);
        let y_lit = ctx.ir_builder().literal(y_var, false);

        let formula = Formula::And(vec![x_lit, y_lit, x_lit2]);

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert_eq!(var_count.get(&x), Some(&2));
        assert_eq!(var_count.get(&y), Some(&1));
    }

    #[test]
    fn test_count_vars_with_empty_formula() {
        let formula = Formula::And(vec![]); // This represents an empty conjunction

        let mut var_count = HashMap::new();
        IndependentVarReducer::count_vars(&formula, &mut var_count);

        assert!(var_count.is_empty());
    }

    fn reduce_inre_non_empty(regex: &Regex, ctx: &mut Context, pol: bool) {
        let var = ctx.make_var("x".to_string(), Sort::String).unwrap();

        let fm = ctx
            .ir_builder()
            .in_re(Pattern::variable(var.as_ref()), regex.clone());
        let lit = Literal::new(fm, pol);
        let fm = Formula::Literal(lit.clone());
        let reducer = IndependentVarReducer::new(&fm);

        match reducer.infer(&lit, true, ctx) {
            Some(subs) => {
                let sub: String = subs
                    .get(var.as_ref())
                    .unwrap()
                    .as_string()
                    .as_constant()
                    .expect("Substitution not well-defined");
                if pol {
                    assert!(
                        regex.accepts(&sub.clone().into()),
                        "Regex {} does not accept word '{}' (length {})",
                        regex,
                        sub,
                        sub.len()
                    );
                } else {
                    assert!(
                        !regex.accepts(&sub.clone().into()),
                        "Regex {} does not accept word '{}' (length {})",
                        regex,
                        sub,
                        sub.len()
                    );
                }
            }
            None => todo!(),
        }
    }

    #[test]
    fn test_reduce_inre_word() {
        let mut ctx = Context::default();
        let regex = ctx.re_builder().word("foo".into());
        reduce_inre_non_empty(&regex, &mut ctx, true);
        reduce_inre_non_empty(&regex, &mut ctx, false);
    }

    #[test]
    fn test_reduce_inre_positive_word_star() {
        let mut ctx = Context::default();
        let foo = ctx.re_builder().word("foo".into());
        let regex = ctx.re_builder().star(foo);
        reduce_inre_non_empty(&regex, &mut ctx, true);
        reduce_inre_non_empty(&regex, &mut ctx, false);
    }

    #[test]
    fn test_reduce_inre_positive_escape_sequence() {
        let mut ctx = Context::default();
        let regex = parse_rust_regex("\x0a", ctx.re_builder()).unwrap();
        reduce_inre_non_empty(&regex, &mut ctx, true);
        reduce_inre_non_empty(&regex, &mut ctx, false);
    }
}
