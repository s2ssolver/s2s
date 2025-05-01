use std::fmt::{self, Display, Formatter};

use indexmap::IndexMap;
use rustsat::types::Lit;

use crate::{
    ast::{error::NodeError, Node, NodeKind},
    context::Context,
    ir::Literal,
    sat::{nlit, plit, pvar, PFormula, PVar},
};

/// A definition is a pair (l, L) where l is a propositional literals and L is theory literal.

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LitDefinition {
    defining: Lit,
    // The IR representation
    literal: Literal,
    // The node representation
    node: Node,
}

impl LitDefinition {
    pub fn new(defining: Lit, node: Node, literal: Literal) -> Self {
        Self {
            defining,
            node,
            literal,
        }
    }

    pub fn defining(&self) -> Lit {
        self.defining
    }

    pub fn defined_lit(&self) -> &Literal {
        &self.literal
    }

    pub fn defined_node(&self) -> &Node {
        &self.node
    }
}

impl Display for LitDefinition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.defining, self.literal)
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
            write!(f, "\n{} -> {}", def.defining, def.literal)?;
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

pub fn build_abstraction(node: &Node, ctx: &mut Context) -> Result<Abstraction, NodeError> {
    // Helper function to recursively abstract a node.
    // If an atomical node is encountered, checks if it is already defined, otherwise defines it.
    fn do_abstract(
        fm: &Node,
        atom_defs: &mut IndexMap<Node, (PVar, Polarity)>,
    ) -> Result<PFormula, NodeError> {
        match fm.kind() {
            NodeKind::And | NodeKind::Or => {
                let mut ps = Vec::new();
                for c in fm.children() {
                    ps.push(do_abstract(c, atom_defs)?);
                }
                let res = match fm.kind() {
                    NodeKind::Or => PFormula::Or(ps),
                    NodeKind::And => PFormula::And(ps),
                    _ => unreachable!(),
                };
                Ok(res)
            }
            _ => {
                if fm.is_literal() {
                    let (pol, atom) = if fm.is_atomic() {
                        (Polarity::Positive, fm)
                    } else {
                        (Polarity::Negative, &fm[0])
                    };
                    debug_assert!(atom.is_atomic());

                    // Check if we have defined this atom before and re-use the defining variable
                    // Otherwise create new one
                    let defining_var = if let Some((v, dpol)) = atom_defs.get_mut(atom) {
                        if *dpol != pol {
                            *dpol = Polarity::Both
                        }
                        *v
                    } else {
                        let v = pvar();
                        atom_defs.insert(atom.clone(), (v, pol));
                        v
                    };
                    Ok(if pol == Polarity::Positive {
                        PFormula::plit(defining_var)
                    } else {
                        PFormula::nlit(defining_var)
                    })
                } else {
                    Err(NodeError::NotInNegationNormalForm(fm.clone()))
                }
            }
        }
    }
    let mut atom_defs = IndexMap::new();
    let skeleton = do_abstract(node, &mut atom_defs)?;
    let mut defs = Vec::with_capacity(atom_defs.len());
    for (atom, (v, pol)) in atom_defs {
        // check if this atom it supported
        if let Some(lit) = ctx.to_ir(&atom) {
            assert!(lit.polarity());
            if pol.positive() {
                let def = LitDefinition::new(plit(v), atom.clone(), lit.clone());
                defs.push(def);
            }
            if pol.negative() {
                let negated = ctx.ast().not(atom);
                let def: LitDefinition = LitDefinition::new(nlit(v), negated, lit.flip_polarity());
                defs.push(def);
            }
        } else {
            // TODO: in the future I would like this check to but done in the engine rather than in the abstraction
            // The abstraction should not have to know which atoms/literals are support and whic aren't
            log::warn!("Ignoring: {}, unsupported", atom)
        }
    }
    Ok(Abstraction::new(skeleton, defs))
}
