use std::{collections::HashMap, rc::Rc};

use crate::{
    repr::ir::{Atom, Formula},
    sat::{nlit, plit, pvar, PFormula, PVar},
};

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
pub struct Definition {
    var: PVar,
    atom: Rc<Atom>,
    polarity: DefinitionType,
}

impl Definition {
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

    /// Returns true if the definition is equivalent.
    pub fn is_equiv(&self) -> bool {
        matches!(self.polarity, DefinitionType::Equivalence)
    }
}

/// An abstraction of a formula, consisting of a skeleton and definitions.
/// Every propositional variable in the skeleton is defined by a definition.
/// By replacing all propositional variables in the skeleton with their definitions, the original formula can be reconstructed.
pub struct Abstraction {
    skeleton: PFormula,
    definitions: HashMap<Rc<Atom>, Definition>, // TODO: Use a Vec instead of a HashMap
}

impl Abstraction {
    pub fn skeleton(&self) -> &PFormula {
        &self.skeleton
    }

    pub fn definitions(&self) -> impl Iterator<Item = &Definition> {
        self.definitions.values()
    }
}

/// Constructs an abstraction of a formula.
/// The construction is done using the Plaisted-Greenbaum transformation.
/// That means that the propositional literal are not equivalent to the atoms, but imply them.
/// For example, if `v` is a propositional variable and `a` is an atom in the formula only occurring with positive polarity, we add the definition `v => a`, but not `-v => -a`.
/// Conversely, if `a` only occurs with negative polarity, we add the definition `-v => -a`, but not `v => a`.
/// If `a` occurs with both polarities, we add the definition `v <=> a`.
pub fn abstract_fm(fm: &Formula) -> Abstraction {
    let mut defs = HashMap::new();
    let skeleton = build(fm, &mut defs);
    Abstraction {
        skeleton,
        definitions: defs,
    }
}

fn build(fm: &Formula, defs: &mut HashMap<Rc<Atom>, Definition>) -> PFormula {
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
                    let def = Definition::new(
                        def_var,
                        lit.atom().clone(),
                        DefinitionType::PositiveImplication,
                    );
                    defs.insert(lit.atom().clone(), def);
                    PFormula::Lit(plit(def_var))
                } else {
                    let def = Definition::new(
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
