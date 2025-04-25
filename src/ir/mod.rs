use std::{fmt::Display, hash::Hash, rc::Rc};

use indexmap::{indexset, IndexSet};

use crate::context::Variable;

/// Conversion from AST to IR
mod convert;
/// Linear Integer Arithmetic Atoms
mod int;
/// String Atoms
mod string;
pub mod util;

pub use convert::convert as convert_to_ir;
pub use int::*;
pub use string::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    pub fn atom(&self) -> &Rc<Atom> {
        &self.atom
    }

    pub fn flip_polarity(&self) -> Self {
        match self.atom().as_ref() {
            Atom::True => Self::new(true, Rc::new(Atom::False)),
            Atom::False => Self::new(true, Rc::new(Atom::True)),
            Atom::Linear(lc) => Self::new(self.pol, Rc::new(Atom::Linear(lc.negate()))),
            _ => Self {
                pol: !self.pol,
                atom: self.atom.clone(),
            },
        }
    }

    pub(crate) fn variables(&self) -> IndexSet<Rc<Variable>> {
        self.atom().variables()
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    True,
    False,
    Boolvar(Rc<Variable>),
    WordEquation(WordEquation),
    InRe(RegularConstraint),
    FactorConstraint(RegularFactorConstraint),
    Linear(LIAConstraint),
}
impl Atom {
    fn variables(&self) -> IndexSet<Rc<Variable>> {
        match self {
            Atom::True | Atom::False => indexset! {},
            Atom::Boolvar(v) => {
                let mut vars = IndexSet::new();
                vars.insert(v.clone());
                vars
            }
            Atom::WordEquation(eq) => eq.variables(),
            Atom::InRe(inre) => inre.lhs().variables(),
            Atom::FactorConstraint(rfc) => rfc.of().variables(),
            Atom::Linear(lc) => lc.variables(),
        }
    }
}
impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::True => write!(f, "true"),
            Atom::False => write!(f, "false"),
            Atom::WordEquation(we) => write!(f, "{}", we),
            Atom::InRe(re) => write!(f, "{}", re),
            Atom::FactorConstraint(fc) => write!(f, "{}", fc),
            Atom::Linear(lc) => write!(f, "{}", lc),
            Atom::Boolvar(v) => write!(f, "{}", v),
        }
    }
}
