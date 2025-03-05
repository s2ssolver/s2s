use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    rc::Rc,
};

use indexmap::IndexSet;

use crate::node::Variable;

mod assignment;

mod int;
mod string;
pub mod util;
pub use assignment::Assignment;
pub use int::*;
pub use string::*;

use super::Id;

#[derive(Debug, Clone)]
pub struct Literal {
    pol: bool,
    atom: Rc<Atom>,
}

impl Literal {
    pub fn positive(atom: Rc<Atom>) -> Self {
        Self { pol: true, atom }
    }

    pub fn negative(atom: Rc<Atom>) -> Self {
        Self { pol: false, atom }
    }

    pub fn new(pol: bool, atom: Rc<Atom>) -> Self {
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

    pub fn id(&self) -> isize {
        if self.pol {
            self.atom.id() as isize
        } else {
            -(self.atom.id() as isize)
        }
    }

    pub fn atom(&self) -> &Rc<Atom> {
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
            write!(f, "¬{}", self.atom)
        }
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for Literal {}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

            AtomKind::FactorConstraint(rfc) => {
                let mut vars = IndexSet::new();
                vars.insert(rfc.of().clone());
                vars
            }
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
    id: Id,
}

impl Atom {
    pub fn new(kind: AtomKind, id: Id) -> Self {
        Self { kind, id }
    }

    pub fn kind(&self) -> &AtomKind {
        &self.kind
    }

    fn id(&self) -> Id {
        self.id
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
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
