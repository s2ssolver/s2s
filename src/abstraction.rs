use std::{
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use indexmap::IndexMap;

use crate::{
    node::{
        canonical::{Atom, Literal},
        error::NodeError,
        Node, NodeKind,
    },
    sat::{nlit, plit, pvar, PFormula, PLit, PVar},
};

/// A definition is a pair (l, L) where l is a propositional literals and L is theory literal.

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LitDefinition {
    defining: PLit,
    defined: Literal,
}

impl LitDefinition {
    pub fn defining(&self) -> PLit {
        self.defining
    }

    pub fn defined(&self) -> &Literal {
        &self.defined
    }
}

impl Display for LitDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.defining, self.defined)
    }
}

pub struct Abstraction {
    skeleton: PFormula,
    /// The set of definitions, indexed by the defined literal.
    definitions: Vec<LitDefinition>,
}

impl Display for Abstraction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.skeleton)?;
        for def in &self.definitions {
            write!(f, "\n{} -> {}", def.defining, def.defined)?;
        }
        Ok(())
    }
}

impl Abstraction {
    pub fn skeleton(&self) -> &PFormula {
        &self.skeleton
    }

    pub fn definitions(&self) -> impl Iterator<Item = &LitDefinition> {
        self.definitions.iter()
    }

    fn new(skeleton: PFormula, definitions: Vec<LitDefinition>) -> Self {
        Self {
            skeleton,
            definitions,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
    Both,
}

impl Polarity {
    fn negative(&self) -> bool {
        matches!(self, Polarity::Negative | Polarity::Both)
    }

    fn positive(&self) -> bool {
        matches!(self, Polarity::Positive | Polarity::Both)
    }
}

pub fn build_abstraction(node: &Node) -> Result<Abstraction, NodeError> {
    // Helper function to recursively abstract a node.
    // If an atomical node is encountered, checks if it is already defined, otherwise defines it.
    fn do_abstract(
        fm: &Node,
        atom_defs: &mut IndexMap<Rc<Atom>, (PVar, Polarity)>,
        undefs: &mut IndexMap<Node, PVar>, // Nodes that cannot be defined as canonical literals
    ) -> Result<PFormula, NodeError> {
        match fm.kind() {
            NodeKind::And | NodeKind::Or => {
                let mut ps = Vec::new();
                for c in fm.children() {
                    ps.push(do_abstract(c, atom_defs, undefs)?);
                }
                let res = match fm.kind() {
                    NodeKind::Or => PFormula::Or(ps),
                    NodeKind::And => PFormula::And(ps),
                    _ => unreachable!(),
                };
                Ok(res)
            }
            NodeKind::Literal(lit) => {
                let atom = lit.atom();
                let pol = if lit.polarity() {
                    Polarity::Positive
                } else {
                    Polarity::Negative
                };
                let v = if let Some((v, dpol)) = atom_defs.get_mut(atom) {
                    if *dpol != pol {
                        *dpol = Polarity::Both;
                    }
                    *v
                } else {
                    let v = pvar();
                    atom_defs.insert(atom.clone(), (v, pol));
                    v
                };
                Ok(if lit.polarity() {
                    PFormula::plit(v)
                } else {
                    PFormula::nlit(v)
                })
            }
            NodeKind::Not => {
                // this is an unsupported negated atom: we need to add a Boolean var which does not define a canonical literal
                let atom = &fm.children()[0];
                debug_assert!(atom.is_atomic());
                let v = if let Some(v) = undefs.get(atom) {
                    *v
                } else {
                    let v = pvar();
                    undefs.insert(atom.clone(), v);
                    v
                };
                Ok(PFormula::nlit(v))
            }
            _ => {
                // this is an unsupported atom: we need to add a Boolean var which does not define a canonical literal
                debug_assert!(fm.is_atomic());
                let v = if let Some(v) = undefs.get(fm) {
                    *v
                } else {
                    let v = pvar();
                    undefs.insert(fm.clone(), v);
                    v
                };
                Ok(PFormula::nlit(v))
            }
        }
    }
    let mut atom_defs = IndexMap::new();
    let mut undefs = IndexMap::new();
    let skeleton = do_abstract(node, &mut atom_defs, &mut undefs)?;
    let mut defs = Vec::with_capacity(atom_defs.len());
    for (atom, (v, pol)) in atom_defs {
        if pol.positive() {
            let def = LitDefinition {
                defining: plit(v),
                defined: Literal::positive(atom.clone()),
            };
            defs.push(def);
        }

        if pol.negative() {
            let def: LitDefinition = LitDefinition {
                defining: nlit(v),
                defined: Literal::negative(atom.clone()),
            };
            defs.push(def);
        }
    }
    Ok(Abstraction::new(skeleton, defs))
}
