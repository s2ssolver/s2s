//! Internal representation of the input formula.
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    rc::Rc,
};

use regulaer::re::Regex;

mod int;
mod string;
mod substitution;
pub use int::{LinearArithTerm, LinearOperator};
pub use string::Pattern;

use crate::ast::{Sort, Sorted, Variable};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum AtomType {
    BoolVar(Variable),
    InRe(Pattern, Regex),
    WordEquation(Pattern, Pattern),
    LinearConstraint(LinearArithTerm, LinearOperator, isize),
}

#[derive(Clone, Debug)]
pub struct Atom {
    id: usize,
    atom: AtomType,
}

impl Atom {
    fn new(id: usize, atom: AtomType) -> Self {
        Self { id, atom }
    }
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Atom {}
impl Hash for Atom {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Literal {
    Pos(Rc<Atom>),
    Neg(Rc<Atom>),
}
impl Literal {
    pub fn polarity(&self) -> bool {
        match self {
            Self::Pos(_) => true,
            Self::Neg(_) => false,
        }
    }
    pub fn atom(&self) -> &Rc<Atom> {
        match self {
            Self::Pos(a) | Self::Neg(a) => a,
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FormulaType {
    Literal(Literal),
    And(Vec<Rc<Formula>>),
    Or(Vec<Rc<Formula>>),
}

#[derive(Clone, Debug)]
pub struct Formula {
    id: usize,
    formula: FormulaType,
}

impl Formula {
    fn new(id: usize, formula: FormulaType) -> Self {
        Self { id, formula }
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Formula {}
impl Hash for Formula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Default)]
pub struct FormulaBuilder {
    registry: HashMap<FormulaType, Rc<Formula>>,
    lit_registry: HashMap<AtomType, Rc<Atom>>,
    next_id: usize,
}

impl FormulaBuilder {
    /// Interns a formula, ensuring it is unique.
    fn intern(&mut self, ttype: FormulaType) -> Rc<Formula> {
        if let Some(existing) = self.registry.get(&ttype) {
            existing.clone()
        } else {
            let fm = Formula::new(self.next_id, ttype.clone());
            self.next_id += 1;
            let rc = Rc::new(fm.clone());
            self.registry.insert(ttype, rc.clone());
            rc
        }
    }

    fn intern_atom(&mut self, atom: AtomType) -> Rc<Atom> {
        if let Some(existing) = self.lit_registry.get(&atom) {
            existing.clone()
        } else {
            let at = Atom::new(self.next_id, atom.clone());
            self.next_id += 1;
            let rc = Rc::new(at.clone());
            self.lit_registry.insert(atom, rc.clone());
            rc
        }
    }

    /// Builds a conjunction of subformulas.
    pub fn and(&mut self, formulas: Vec<Rc<Formula>>) -> Rc<Formula> {
        self.intern(FormulaType::And(formulas))
    }

    /// Builds a disjunction of subformulas.
    pub fn or(&mut self, formulas: Vec<Rc<Formula>>) -> Rc<Formula> {
        self.intern(FormulaType::Or(formulas))
    }

    pub fn literal(&mut self, atom: Rc<Atom>, polarity: bool) -> Rc<Formula> {
        let lit = if polarity {
            Literal::Pos(atom)
        } else {
            Literal::Neg(atom)
        };
        self.intern(FormulaType::Literal(lit))
    }

    pub fn bool_var(&mut self, var: Variable) -> Rc<Atom> {
        assert!(var.sort() == Sort::Bool);
        let atom = AtomType::BoolVar(var);
        self.intern_atom(atom)
    }

    pub fn word_equation(&mut self, lhs: Pattern, rhs: Pattern) -> Rc<Atom> {
        let atom = AtomType::WordEquation(lhs, rhs);
        self.intern_atom(atom)
    }

    pub fn in_re(&mut self, pat: Pattern, re: Regex) -> Rc<Atom> {
        let atom = AtomType::InRe(pat, re);
        self.intern_atom(atom)
    }

    pub fn linear_constraint(
        &mut self,
        lhs: LinearArithTerm,
        op: LinearOperator,
        rhs: isize,
    ) -> Rc<Atom> {
        let atom = AtomType::LinearConstraint(lhs, op, rhs);
        self.intern_atom(atom)
    }
}
