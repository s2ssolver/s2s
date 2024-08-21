//! Internal representation of the input formula.
use std::{collections::HashMap, fmt::Display, hash::Hash, rc::Rc};

use regulaer::re::Regex;

mod int;
mod string;
mod substitution;
pub use int::{LinearArithTerm, LinearOperator};
pub use string::Pattern;
pub use substitution::*;

use super::Variable;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum AtomType {
    /// A boolean variable.
    BoolVar(Rc<Variable>),
    /// A constant boolean value.
    BoolConst(bool),

    /// A regular constraint.
    InRe(Pattern, Regex),
    /// A word equation.
    WordEquation(Pattern, Pattern),

    /// PrefixOf
    PrefixOf(Pattern, Pattern),
    /// SuffixOf
    SuffixOf(Pattern, Pattern),
    /// Contains
    Contains(Pattern, Pattern),

    /// A linear constraint.
    LinearConstraint(LinearArithTerm, LinearOperator, isize),
}
impl Display for AtomType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomType::BoolVar(v) => write!(f, "{}", v),
            AtomType::BoolConst(b) => write!(f, "{}", b),
            AtomType::InRe(p, r) => write!(f, "{} ∈ {}", p, r),
            AtomType::WordEquation(l, r) => write!(f, "{} = {}", l, r),
            AtomType::PrefixOf(l, r) => write!(f, "{} ⊑ {}", l, r),
            AtomType::SuffixOf(l, r) => write!(f, "{} ⊒ {}", l, r),
            AtomType::Contains(l, r) => write!(f, "{} contains {}", l, r),
            AtomType::LinearConstraint(l, o, r) => write!(f, "{} {} {}", l, o, r),
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
    /// A theory literal.
    Literal(Literal),
    /// A conjunction of subformulas.
    And(Vec<Formula>),
    /// A disjunction of subformulas.
    Or(Vec<Formula>),
}
impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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

    pub fn bool_const(&mut self, value: bool) -> Rc<Atom> {
        let bool_const = AtomType::BoolConst(value);
        self.register_atom(bool_const)
    }

    pub fn word_equation(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let eq = AtomType::WordEquation(lhs, rhs);
        self.register_atom(eq)
    }

    pub fn in_re(&mut self, lhs: Pattern, rhs: Regex) -> Rc<Atom> {
        let in_re = AtomType::InRe(lhs, rhs);
        self.register_atom(in_re)
    }

    pub fn prefix_of(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let prefix_of = AtomType::PrefixOf(lhs, rhs);
        self.register_atom(prefix_of)
    }

    pub fn suffix_of(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let suffix_of = AtomType::SuffixOf(lhs, rhs);
        self.register_atom(suffix_of)
    }

    pub fn contains(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let contains = AtomType::Contains(lhs, rhs);
        self.register_atom(contains)
    }

    pub fn linear_constraint(
        &mut self,
        lhs: LinearArithTerm,
        op: LinearOperator,
        rhs: isize,
    ) -> Rc<Atom> {
        let linear_constraint = AtomType::LinearConstraint(lhs, op, rhs);
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
