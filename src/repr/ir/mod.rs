//! Internal representation of the input formula.
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    rc::Rc,
};

use indexmap::IndexSet;
use regulaer::re::Regex;

mod int;
mod string;
mod substitution;
pub mod util;

pub use int::*;
pub use string::*;
pub use substitution::*;

use super::Variable;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum AtomType {
    /// A boolean variable.
    BoolVar(Rc<Variable>),

    /// A regular constraint.
    InRe(RegularConstraint),
    /// A word equation.
    WordEquation(WordEquation),

    /// PrefixOf
    PrefixOf(PrefixOf),
    /// SuffixOf
    SuffixOf(SuffixOf),
    /// Contains
    Contains(Contains),

    /// A linear constraint.
    LinearConstraint(LinearConstraint),
}
impl AtomType {
    pub fn variables(&self) -> IndexSet<Variable> {
        match self {
            AtomType::BoolVar(v) => {
                let mut vars = IndexSet::new();
                vars.insert(v.as_ref().clone());
                vars
            }
            AtomType::InRe(inre) => inre.variables(),
            AtomType::WordEquation(eq) => eq.variables(),
            AtomType::PrefixOf(p) => p.variables(),
            AtomType::SuffixOf(s) => s.variables(),
            AtomType::Contains(c) => c.variables(),
            AtomType::LinearConstraint(lc) => lc.variables(),
        }
    }
    pub fn constants(&self) -> IndexSet<char> {
        match self {
            AtomType::BoolVar(_) | AtomType::LinearConstraint(_) => IndexSet::new(),
            AtomType::InRe(inre) => inre.constants(),
            AtomType::WordEquation(eq) => eq.constants(),
            AtomType::PrefixOf(p) => p.constants(),
            AtomType::SuffixOf(s) => s.constants(),
            AtomType::Contains(c) => c.constants(),
        }
    }
}
impl Display for AtomType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomType::BoolVar(v) => write!(f, "{}", v),
            AtomType::InRe(rc) => write!(f, "{}", rc),
            AtomType::WordEquation(eq) => write!(f, "{}", eq),
            AtomType::PrefixOf(c) => write!(f, "{}", c),
            AtomType::SuffixOf(c) => write!(f, "{}", c),
            AtomType::Contains(c) => write!(f, "{}", c),
            AtomType::LinearConstraint(lc) => write!(f, "{}", lc),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Atom {
    ttype: AtomType,
    id: usize,
}
impl Hash for Atom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Atom {}
impl Atom {
    fn new(ttype: AtomType, id: usize) -> Self {
        Self { ttype, id }
    }
    pub fn get_type(&self) -> &AtomType {
        &self.ttype
    }
    pub fn into_type(self) -> AtomType {
        self.ttype
    }
    pub fn variables(&self) -> IndexSet<Variable> {
        self.ttype.variables()
    }
    pub fn constants(&self) -> IndexSet<char> {
        self.ttype.constants()
    }
}
impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ttype)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    /// A positive literal.
    Positive(Rc<Atom>),
    /// A negative literal.
    Negative(Rc<Atom>),
}
impl Literal {
    pub fn new(atom: Rc<Atom>, polarity: bool) -> Self {
        if polarity {
            Literal::Positive(atom)
        } else {
            Literal::Negative(atom)
        }
    }

    pub fn id(&self) -> isize {
        match self {
            Literal::Positive(a) => a.id as isize,
            Literal::Negative(a) => -(a.id as isize),
        }
    }

    pub fn atom(&self) -> &Rc<Atom> {
        match self {
            Literal::Positive(a) => a,
            Literal::Negative(a) => a,
        }
    }

    pub fn into_atom(self) -> Rc<Atom> {
        match self {
            Literal::Positive(a) => a,
            Literal::Negative(a) => a,
        }
    }

    /// The polarity of the literal.
    pub fn polarity(&self) -> bool {
        match self {
            Literal::Positive(_) => true,
            Literal::Negative(_) => false,
        }
    }

    /// Returns the inverse of the literal.
    /// The inverse of a positive literal is a negative literal and vice versa.
    pub fn inverse(&self) -> Literal {
        match self {
            Literal::Positive(a) => Literal::Negative(a.clone()),
            Literal::Negative(a) => Literal::Positive(a.clone()),
        }
    }

    /// Returns the set of variables in the literal.
    pub fn variables(&self) -> IndexSet<Variable> {
        self.atom().variables()
    }

    /// Returns the set of constants in the literal.
    pub fn constants(&self) -> IndexSet<char> {
        self.atom().constants()
    }
}
impl Hash for Literal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}
impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Positive(a) => write!(f, "{}", a),
            Literal::Negative(a) => write!(f, "¬({})", a),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Formula {
    /// The constant true.
    True,
    /// The constant false.
    False,
    /// A theory literal.
    Literal(Literal),
    /// A conjunction of subformulas.
    And(Vec<Formula>),
    /// A disjunction of subformulas.
    Or(Vec<Formula>),
}
impl Formula {
    /// Reduces the formula by resolving the following Boolean equivalences:
    /// - `true ∧ x` = `x`
    /// - `false ∧ x` = `false`
    /// - `true ∨ x` = `true`
    /// - `false ∨ x` = `x`
    /// - `A ∧ A` = `x`
    /// - `A ∨ A` = `x`
    /// - `A ∧ ¬A` = `false`
    /// - `A ∨ ¬A` = `true`
    /// Additionally, reduces all constant literals to their truth value.
    pub fn reduce(self) -> Formula {
        match self {
            Formula::True | Formula::False => self,
            Formula::Literal(lit) => Self::reduce_literal(lit),
            Formula::And(fs) => Self::reduce_conjunction(fs),
            Formula::Or(fs) => Self::reduce_disjunction(fs),
        }
    }

    fn reduce_literal(lit: Literal) -> Formula {
        match lit.is_constant() {
            Some(true) => Formula::True,   // `true` literal
            Some(false) => Formula::False, // `false` literal
            None => Formula::Literal(lit), // Non-constant literal
        }
    }

    fn reduce_conjunction(formulas: Vec<Formula>) -> Formula {
        let mut reduced = HashSet::new();
        let mut seen_lits = HashSet::new();

        for f in formulas {
            let f = f.reduce();
            match f {
                Formula::False => return Formula::False, // `false ∧ x` = `false`
                Formula::True => continue,               // Skip `true`
                Formula::Literal(ref lit) => {
                    let inv = lit.inverse();
                    if seen_lits.contains(&inv) {
                        return Formula::False; // `A ∧ ¬A` = `false`
                    }
                    seen_lits.insert(lit.clone());
                }
                _ => {}
            }
            reduced.insert(f);
        }

        match reduced.len() {
            0 => Formula::True, // If all were `true`, return `true`
            1 => reduced.into_iter().next().unwrap(),
            _ => Formula::And(reduced.into_iter().collect()),
        }
    }

    fn reduce_disjunction(formulas: Vec<Formula>) -> Formula {
        let mut reduced = HashSet::new();
        let mut seen_lits = HashSet::new();

        for f in formulas {
            let f = f.reduce();
            match f {
                Formula::True => return Formula::True, // `true ∨ x` = `true`
                Formula::False => continue,            // Skip `false`
                Formula::Literal(ref lit) => {
                    let inv = lit.inverse();
                    if seen_lits.contains(&inv) {
                        return Formula::True; // `A ∨ ¬A` = `true`
                    }
                    seen_lits.insert(lit.clone());
                }
                _ => {}
            }
            reduced.insert(f);
        }

        match reduced.len() {
            0 => Formula::False, // If all were `false`, return `false`
            1 => reduced.into_iter().next().unwrap(),
            _ => Formula::Or(reduced.into_iter().collect()),
        }
    }

    pub fn literals(&self) -> LiteralIterator {
        LiteralIterator::new(self, false)
    }

    /// Returns an iterator over the literals entailed by the formula.
    /// An entailed literal must be satisfied by any model of the formula.
    /// The iterator returend by this function iterators only over a subset of the entailed literals by visiting only such literals that are reachable by only following conjunctions.
    pub fn entailed_literals(&self) -> LiteralIterator {
        LiteralIterator::new(self, true)
    }

    /// Checks if the formula entails the given literal.
    /// If true, the formula implies the literal.
    /// If false, it is unknown if the formula implies the literal.
    pub(crate) fn entails(&self, l: &&Literal) -> bool {
        self.entailed_literals().any(|lit| lit == *l)
    }
}
impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Formula::True => write!(f, "⊤"),
            Formula::False => write!(f, "⊥"),
            Formula::Literal(lit) => write!(f, "{}", lit),
            Formula::And(es) => {
                let mut iter = es.iter();
                if let Some(e) = iter.next() {
                    write!(f, "({}", e)?;
                    for e in iter {
                        write!(f, " ∧ {}", e)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Formula::Or(es) => {
                let mut iter = es.iter();
                if let Some(e) = iter.next() {
                    write!(f, "({}", e)?;
                    for e in iter {
                        write!(f, " ∨ {}", e)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

pub trait ConstReducible {
    /// Checks if the formula constant.
    /// If the formula is constant, returns the constant truth value.
    /// If the formula is not constant, returns None.
    fn is_constant(&self) -> Option<bool>;
}

impl ConstReducible for Atom {
    fn is_constant(&self) -> Option<bool> {
        match self.get_type() {
            AtomType::BoolVar(_) => None,
            AtomType::InRe(r) => r.is_constant(),
            AtomType::WordEquation(w) => w.is_constant(),
            AtomType::PrefixOf(p) => p.is_constant(),
            AtomType::SuffixOf(s) => s.is_constant(),
            AtomType::Contains(c) => c.is_constant(),
            AtomType::LinearConstraint(lc) => lc.is_constant(),
        }
    }
}

impl ConstReducible for Literal {
    fn is_constant(&self) -> Option<bool> {
        self.atom()
            .is_constant()
            .map(|c| if self.polarity() { c } else { !c })
    }
}

#[derive(Default)]
pub struct IrBuilder {
    registry: HashMap<AtomType, Rc<Atom>>,
}

impl IrBuilder {
    fn register_atom(&mut self, atom: AtomType) -> Rc<Atom> {
        if let Some(atom) = self.registry.get(&atom) {
            return atom.clone();
        } else {
            let id = self.registry.len();
            let atom = Rc::new(Atom::new(atom, id));
            self.registry.insert(atom.get_type().clone(), atom.clone());
            atom
        }
    }

    pub fn bool_var(&mut self, var: Rc<Variable>) -> Rc<Atom> {
        let bool_var = AtomType::BoolVar(var);
        self.register_atom(bool_var)
    }

    pub fn word_equation(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let eq = AtomType::WordEquation(WordEquation::new(lhs, rhs));
        self.register_atom(eq)
    }

    pub fn in_re(&mut self, lhs: Pattern, re: Regex) -> Rc<Atom> {
        let in_re = AtomType::InRe(RegularConstraint::new(lhs, re));
        self.register_atom(in_re)
    }

    pub fn prefix_of(&mut self, prefix: Pattern, of: Pattern) -> Rc<Atom> {
        let prefix_of = AtomType::PrefixOf(PrefixOf::new(prefix, of));
        self.register_atom(prefix_of)
    }

    pub fn suffix_of(&mut self, suffix: Pattern, of: Pattern) -> Rc<Atom> {
        let suffix_of = AtomType::SuffixOf(SuffixOf::new(suffix, of));
        self.register_atom(suffix_of)
    }

    pub fn contains(&mut self, haystack: Pattern, needle: Pattern) -> Rc<Atom> {
        let contains = AtomType::Contains(Contains::new(needle, haystack));
        self.register_atom(contains)
    }

    pub fn linear_constraint(
        &mut self,
        lhs: LinearArithTerm,
        op: LinearOperator,
        rhs: isize,
    ) -> Rc<Atom> {
        let linear_constraint = AtomType::LinearConstraint(LinearConstraint::new(lhs, op, rhs));
        self.register_atom(linear_constraint)
    }

    pub fn and(&self, formulas: Vec<Formula>) -> Formula {
        Formula::And(formulas)
    }

    pub fn or(&self, formulas: Vec<Formula>) -> Formula {
        Formula::Or(formulas)
    }

    pub fn literal(&self, atom: Rc<Atom>, polarity: bool) -> Formula {
        let literal = if polarity {
            Literal::Positive(atom)
        } else {
            Literal::Negative(atom)
        };
        Formula::Literal(literal)
    }

    pub fn plit(&self, atom: Rc<Atom>) -> Formula {
        self.literal(atom, true)
    }

    pub fn nlit(&self, atom: Rc<Atom>) -> Formula {
        self.literal(atom, false)
    }
}

pub struct LiteralIterator<'a> {
    entailed_only: bool,
    stack: Vec<&'a Formula>,
}

impl<'a> LiteralIterator<'a> {
    pub fn new(formula: &'a Formula, entailed_only: bool) -> Self {
        let stack = vec![formula];
        LiteralIterator {
            stack,
            entailed_only,
        }
    }
}

impl<'a> Iterator for LiteralIterator<'a> {
    type Item = &'a Literal;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(formula) = self.stack.pop() {
            match formula {
                Formula::True | Formula::False => continue,
                Formula::Literal(lit) => return Some(lit),
                Formula::And(fs) => {
                    self.stack.extend(fs.iter());
                }
                Formula::Or(fs) => {
                    if !self.entailed_only {
                        self.stack.extend(fs.iter());
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use crate::repr::Sort;

    use super::*;
    #[test]
    fn test_reduce_true() {
        let formula = Formula::True;
        assert_eq!(formula.reduce(), Formula::True);
    }

    #[test]
    fn test_reduce_false() {
        let formula = Formula::False;
        assert_eq!(formula.reduce(), Formula::False);
    }

    #[test]
    fn test_reduce_literal() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x));

        let formula = Formula::Literal(lit.clone());
        assert_eq!(formula.reduce(), Formula::Literal(lit));
    }

    #[test]
    fn test_reduce_and_with_true() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x));

        let formula = Formula::And(vec![Formula::True, Formula::Literal(lit.clone())]);
        assert_eq!(formula.reduce(), Formula::Literal(lit));
    }

    #[test]
    fn test_reduce_and_with_false() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x));

        let formula = Formula::And(vec![Formula::False, Formula::Literal(lit)]);
        assert_eq!(formula.reduce(), Formula::False);
    }

    #[test]
    fn test_reduce_or_with_true() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x));

        let formula = Formula::Or(vec![Formula::True, Formula::Literal(lit)]);
        assert_eq!(formula.reduce(), Formula::True);
    }

    #[test]
    fn test_reduce_or_with_false() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x.clone()));

        let formula = Formula::Or(vec![Formula::False, Formula::Literal(lit.clone())]);
        assert_eq!(formula.reduce(), Formula::Literal(lit));
    }

    #[test]
    fn test_reduce_and_with_duplicate_literal() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x.clone()));

        let formula = Formula::And(vec![
            Formula::Literal(lit.clone()),
            Formula::Literal(lit.clone()),
        ]);
        assert_eq!(formula.reduce(), Formula::Literal(lit));
    }

    #[test]
    fn test_reduce_or_with_duplicate_literal() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit = Literal::Positive(builder.bool_var(var_x.clone()));

        let formula = Formula::Or(vec![
            Formula::Literal(lit.clone()),
            Formula::Literal(lit.clone()),
        ]);
        assert_eq!(formula.reduce(), Formula::Literal(lit));
    }

    #[test]
    fn test_reduce_and_with_complementary_literals() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit1 = Literal::Positive(builder.bool_var(var_x.clone()));
        let lit2 = Literal::Negative(builder.bool_var(var_x));

        let formula = Formula::And(vec![Formula::Literal(lit1), Formula::Literal(lit2)]);
        assert_eq!(formula.reduce(), Formula::False);
    }

    #[test]
    fn test_reduce_or_with_complementary_literals() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let lit1 = Literal::Positive(builder.bool_var(var_x.clone()));
        let lit2 = Literal::Negative(builder.bool_var(var_x));

        let formula = Formula::Or(vec![Formula::Literal(lit1), Formula::Literal(lit2)]);
        assert_eq!(formula.reduce(), Formula::True);
    }

    #[test]
    fn test_reduce_complex_and() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let var_y = Rc::new(Variable::new(1, "y".to_string(), Sort::Bool));
        let lit1 = Literal::Positive(builder.bool_var(var_x.clone()));
        let lit2 = Literal::Positive(builder.bool_var(var_y.clone()));

        let formula = Formula::And(vec![
            Formula::Literal(lit1.clone()),
            Formula::True,
            Formula::Literal(lit2.clone()),
            Formula::Literal(lit1.clone()),
        ]);
        assert_eq!(
            formula.reduce(),
            Formula::And(vec![Formula::Literal(lit1), Formula::Literal(lit2)])
        );
    }

    #[test]
    fn test_reduce_complex_or() {
        let mut builder = IrBuilder::default();
        let var_x = Rc::new(Variable::new(0, "x".to_string(), Sort::Bool));
        let var_y = Rc::new(Variable::new(1, "y".to_string(), Sort::Bool));
        let lit1 = Literal::Positive(builder.bool_var(var_x.clone()));
        let lit2 = Literal::Positive(builder.bool_var(var_y.clone()));

        let formula = Formula::Or(vec![
            Formula::Literal(lit1.clone()),
            Formula::False,
            Formula::Literal(lit2.clone()),
            Formula::Literal(lit1.clone()),
        ]);
        assert_eq!(
            formula.reduce(),
            Formula::Or(vec![Formula::Literal(lit1), Formula::Literal(lit2)])
        );
    }
}
