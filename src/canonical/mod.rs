use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    rc::Rc,
};

use indexmap::IndexSet;

use crate::node::{Node, Variable};

mod assignment;
mod canonicalize;
mod int;
mod string;
pub mod util;
pub use assignment::Assignment;
pub use int::*;
pub use string::*;

pub use canonicalize::canonicalize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FormulaKind {
    And(Vec<Formula>),
    Or(Vec<Formula>),
    /// The node represents a literal.
    Literal(Literal),
    /// Node represents an unsupported construct.
    /// Unsupported here means it has no direct translation to a formula in canonical form
    Unsupported(Node),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Formula {
    kind: FormulaKind,
    node: Node,
}

impl Formula {
    fn new(kind: FormulaKind, node: Node) -> Self {
        Self { kind, node }
    }

    fn unsupported(node: Node) -> Self {
        Self {
            kind: FormulaKind::Unsupported(node.clone()),
            node,
        }
    }

    pub fn kind(&self) -> &FormulaKind {
        &self.kind
    }

    pub fn node(&self) -> &Node {
        &self.node
    }

    pub fn vars(&self) -> IndexSet<Rc<Variable>> {
        match self.kind() {
            FormulaKind::And(children) | FormulaKind::Or(children) => {
                children.iter().flat_map(|f| f.vars()).collect()
            }
            FormulaKind::Literal(lit) => lit.variables(),
            FormulaKind::Unsupported(_) => IndexSet::new(),
        }
    }

    pub fn entailed_lits(&self) -> IndexSet<Literal> {
        match self.kind() {
            FormulaKind::And(children) => children.iter().flat_map(|f| f.entailed_lits()).collect(),
            FormulaKind::Or(_) | FormulaKind::Unsupported(_) => IndexSet::new(),
            FormulaKind::Literal(lit) => {
                let mut lits = IndexSet::new();
                lits.insert(lit.clone());
                lits
            }
        }
    }

    pub fn literals(&self) -> IndexSet<Literal> {
        match self.kind() {
            FormulaKind::And(children) => children.iter().flat_map(|f| f.literals()).collect(),
            FormulaKind::Or(children) => children.iter().flat_map(|f| f.literals()).collect(),
            FormulaKind::Literal(lit) => {
                let mut lits = IndexSet::new();
                lits.insert(lit.clone());
                lits
            }
            FormulaKind::Unsupported(_) => IndexSet::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    pol: bool,
    atom: Atom,
}

impl Literal {
    pub fn positive(atom: Atom) -> Self {
        Self { pol: true, atom }
    }

    pub fn negative(atom: Atom) -> Self {
        Self { pol: false, atom }
    }

    fn new(pol: bool, atom: Atom) -> Self {
        Self { pol, atom }
    }

    pub fn polarity(&self) -> bool {
        self.pol
    }

    pub fn inverted(&self) -> Self {
        Self {
            pol: !self.pol,
            atom: self.atom.clone(),
        }
    }

    pub fn atom(&self) -> &Atom {
        &self.atom
    }

    pub fn flip_polarity(&self) -> Self {
        Self {
            pol: !self.pol,
            atom: self.atom.clone(),
        }
    }

    pub(crate) fn variables(&self) -> IndexSet<Rc<Variable>> {
        self.atom().kind().variables()
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.pol {
            write!(f, "{}", self.atom)
        } else {
            write!(f, "!({})", self.atom)
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub enum AtomKind {
    Boolvar(Rc<Variable>),
    WordEquation(WordEquation),
    InRe(RegularConstraint),
    FactorConstraint(RegularFactorConstraint),
    Linear(LinearConstraint),
}
impl AtomKind {
    fn variables(&self) -> IndexSet<Rc<Variable>> {
        match self {
            AtomKind::Boolvar(v) => {
                let mut vars = IndexSet::new();
                vars.insert(v.clone());
                vars
            }
            AtomKind::WordEquation(eq) => eq.variables(),
            AtomKind::InRe(inre) => {
                let mut vars = IndexSet::new();
                vars.insert(inre.lhs().clone());
                vars
            }

            AtomKind::FactorConstraint(_fc) => todo!(),
            AtomKind::Linear(lc) => lc.variables(),
        }
    }
}
impl Display for AtomKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomKind::WordEquation(we) => write!(f, "{}", we),
            AtomKind::InRe(re) => write!(f, "{}", re),
            AtomKind::FactorConstraint(fc) => write!(f, "{}", fc),
            AtomKind::Linear(lc) => write!(f, "{}", lc),
            AtomKind::Boolvar(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Atom {
    kind: AtomKind,
    node: Node,
}

impl Atom {
    pub fn new(kind: AtomKind, node: Node) -> Self {
        Self { kind, node }
    }

    pub fn kind(&self) -> &AtomKind {
        &self.kind
    }
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}
impl Eq for Atom {}
impl Hash for Atom {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node.hash(state);
    }
}
impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}
