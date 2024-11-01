use std::{
    collections::HashMap,
    fmt,
    fmt::{Display, Formatter},
    rc::Rc,
};

use indexmap::IndexMap;

use crate::{
    ir::{Atom, Formula},
    node::{error::NodeError, Node, NodeKind, NodeManager},
    sat::{nlit, plit, pvar, PFormula, PLit, PVar},
};

/// A definition is a pair (l, L) where l is a propositional literals and L is theory literal.

pub struct LitDefinition {
    defining: PLit,
    defined: Node,
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

pub fn abstract_node(node: &Node, mngr: &mut NodeManager) -> Result<Abstraction, NodeError> {
    // Helper function to recursively abstract a node.
    // If an atomical node is encountered, checks if it is already defined, otherwise defines it.
    fn do_abstract(
        node: &Node,
        atom_defs: &mut IndexMap<Node, (PVar, Polarity)>,
    ) -> Result<PFormula, NodeError> {
        if node.is_atomic() {
            let v = if let Some((v, pol)) = atom_defs.get_mut(node) {
                if *pol == Polarity::Negative {
                    *pol = Polarity::Both;
                }
                *v
            } else {
                let v = pvar();
                atom_defs.insert(node.clone(), (v, Polarity::Positive));
                v
            };
            return Ok(PFormula::plit(v));
        }
        match node.kind() {
            NodeKind::Or | NodeKind::And => {
                let mut ps = Vec::new();
                for c in node.children() {
                    ps.push(do_abstract(c, atom_defs)?);
                }
                let res = match node.kind() {
                    NodeKind::Or => PFormula::Or(ps),
                    NodeKind::And => PFormula::And(ps),
                    _ => unreachable!(),
                };
                Ok(res)
            }

            NodeKind::Not => {
                debug_assert!(node.children().len() == 1);
                let negated = &node[0];
                debug_assert!(negated.is_atomic());
                let v = if let Some((v, pol)) = atom_defs.get_mut(negated) {
                    if *pol == Polarity::Positive {
                        *pol = Polarity::Both;
                    }
                    *v
                } else {
                    let v = pvar();
                    atom_defs.insert(negated.clone(), (v, Polarity::Negative));
                    v
                };
                // -v --> -A
                Ok(PFormula::nlit(v))
            }
            _ if node.is_literal() => unreachable!(),
            _ => Err(NodeError::NotInNegationNormalForm(node.clone())),
        }
    }
    let mut atom_defs = IndexMap::new();
    let skeleton = do_abstract(node, &mut atom_defs)?;
    let mut defs = Vec::with_capacity(atom_defs.len());
    for (atom, (v, pol)) in atom_defs {
        debug_assert!(atom.is_atomic(), "Cannot define non-atomic node {}", atom);
        if pol.positive() {
            let def = LitDefinition {
                defining: plit(v),
                defined: atom.clone(),
            };
            defs.push(def);
        }

        if pol.negative() {
            let lit = mngr.not(atom);
            let def: LitDefinition = LitDefinition {
                defining: nlit(v),
                defined: lit.clone(),
            };
            defs.push(def);
        }
    }
    Ok(Abstraction::new(skeleton, defs))
}

// --------

/// The type of the definition.
/// Positive implication: `v` implies `a`
/// Negative implication: not `v` implies not `a`
/// Equivalence: `v` is equivalent to `a`
#[derive(Debug, Clone)]
pub enum DefinitionType {
    PositiveImplication,
    NegativeImplication,
    Equivalence,
}

/// A definition of an atom by a propositiona variable.
/// The definitions together with the Boolean skeleton of the formula is equisatifiable to the original formula.
/// A definition is a propositiona variable `v` and an atom `a` such that either
/// - `v` implies `a` (positive implication)
/// - not `v` implies not `a` (negative implication)
/// - `v` is equivalent to `a` (equivalence)
#[derive(Debug, Clone)]
pub struct DefinitionOld {
    var: PVar,
    atom: Rc<Atom>,
    polarity: DefinitionType,
}

impl DefinitionOld {
    fn new(var: PVar, atom: Rc<Atom>, polarity: DefinitionType) -> Self {
        Self {
            var,
            atom,
            polarity,
        }
    }

    pub fn def_var(&self) -> PVar {
        self.var
    }

    pub fn atom(&self) -> &Rc<Atom> {
        &self.atom
    }

    /// Makes the definition equivalent to the atom.
    /// That means, the polarity of the definitition is both positive and negative.
    pub fn equiv(&mut self) {
        self.polarity = DefinitionType::Equivalence;
    }

    /// Returns true if the definition is positively.
    /// Meaning the def_var implies the atom.
    pub fn is_pos(&self) -> bool {
        matches!(
            self.polarity,
            DefinitionType::PositiveImplication | DefinitionType::Equivalence
        )
    }

    /// Returns true if the definition is negatively.
    /// Meaning the negation of def_var implies the negation of the atom.
    pub fn is_neg(&self) -> bool {
        matches!(
            self.polarity,
            DefinitionType::NegativeImplication | DefinitionType::Equivalence
        )
    }
}

impl Display for DefinitionOld {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.polarity {
            DefinitionType::PositiveImplication => write!(f, "{} => {}", self.var, self.atom),
            DefinitionType::NegativeImplication => write!(f, "-{} => -{}", self.var, self.atom),
            DefinitionType::Equivalence => write!(f, "{} <=> {}", self.var, self.atom),
        }
    }
}

/// An abstraction of a formula, consisting of a skeleton and definitions.
/// Every propositional variable in the skeleton is defined by a definition.
/// By replacing all propositional variables in the skeleton with their definitions, the original formula can be reconstructed.
pub struct AbstractionOld {
    skeleton: PFormula,
    definitions: HashMap<Rc<Atom>, DefinitionOld>, // TODO: Use a Vec instead of a HashMap
}

impl AbstractionOld {
    pub fn skeleton(&self) -> &PFormula {
        &self.skeleton
    }

    pub fn definitions(&self) -> impl Iterator<Item = &DefinitionOld> {
        self.definitions.values()
    }
}

/// Constructs an abstraction of a formula.
/// The construction is done using the Plaisted-Greenbaum transformation.
/// That means that the propositional literal are not equivalent to the atoms, but imply them.
/// For example, if `v` is a propositional variable and `a` is an atom in the formula only occurring with positive polarity, we add the definition `v => a`, but not `-v => -a`.
/// Conversely, if `a` only occurs with negative polarity, we add the definition `-v => -a`, but not `v => a`.
/// If `a` occurs with both polarities, we add the definition `v <=> a`.
pub fn abstract_fm(fm: &Formula) -> AbstractionOld {
    let mut defs = HashMap::new();
    let skeleton = build(fm, &mut defs);
    AbstractionOld {
        skeleton,
        definitions: defs,
    }
}

fn build(fm: &Formula, defs: &mut HashMap<Rc<Atom>, DefinitionOld>) -> PFormula {
    match fm {
        Formula::True | Formula::False => panic!("Cannot abstract Boolean constants"),
        Formula::Literal(lit) => {
            if let Some(def) = defs.get_mut(lit.atom()) {
                if lit.polarity() {
                    if !def.is_pos() {
                        def.equiv();
                    }
                    PFormula::plit(def.def_var())
                } else {
                    if !def.is_neg() {
                        def.equiv();
                    }
                    PFormula::nlit(def.def_var())
                }
            } else {
                let def_var = pvar();
                if lit.polarity() {
                    let def = DefinitionOld::new(
                        def_var,
                        lit.atom().clone(),
                        DefinitionType::PositiveImplication,
                    );
                    defs.insert(lit.atom().clone(), def);
                    PFormula::Lit(plit(def_var))
                } else {
                    let def = DefinitionOld::new(
                        def_var,
                        lit.atom().clone(),
                        DefinitionType::NegativeImplication,
                    );
                    defs.insert(lit.atom().clone(), def);
                    PFormula::Lit(nlit(def_var))
                }
            }
        }
        Formula::And(rs) => {
            let mut ps = Vec::new();
            for r in rs {
                ps.push(build(r, defs));
            }
            PFormula::And(ps)
        }
        Formula::Or(or) => {
            let mut ps = Vec::new();
            for r in or {
                ps.push(build(r, defs));
            }
            PFormula::Or(ps)
        }
    }
}
