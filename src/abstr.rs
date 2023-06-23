//! The abstraction module. Provide functions to abstract formulas into a Boolean skeleton and a set of definitional Boolean variables.

use indexmap::IndexMap;

use crate::{
    error::Error,
    instance::Instance,
    model::{
        formula::{Atom, Formula, Predicate},
        Sort, Variable,
    },
};

/// The type of a definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefinitionType {
    /// A definition of the form `p <=> f`.
    Equivalence,
    /// A definition of the form `p => f`.
    Positive,
    /// A definition of the form `!p => !f`.
    Negative,
}

/// A defintion consits of a Boolean variable, the predicate it defines, and the type of the definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Definition {
    var: Variable,
    pred: Predicate,
    def_type: DefinitionType,
}

impl Definition {
    /// Creates a new definition.
    pub fn new(var: Variable, pred: Predicate, def_type: DefinitionType) -> Self {
        Self {
            var,
            pred,
            def_type,
        }
    }

    /// Returns the Boolean variable of the definition.
    pub fn get_var(&self) -> &Variable {
        &self.var
    }

    /// Returns the predicate of the definition.
    pub fn get_pred(&self) -> &Predicate {
        &self.pred
    }

    /// Returns the type of the definition.
    #[allow(dead_code)]
    pub fn get_def_type(&self) -> &DefinitionType {
        &self.def_type
    }
}

/// A set of [Defintion]s. Definitions are index by their defining Boolean variable.
/// Adding a definitions make sure that the definitions are consistent. That is,
/// if a predicate is defined by a variable, then it is not defined by another variable.
/// A predicate is defined either positively, negatively, or by an equivalence.
#[derive(Debug, Default)]
pub struct Definitions {
    /// The definitions indexed by their Boolean variable.
    var2def: IndexMap<Variable, Definition>,
}

impl Definitions {
    /// If the predicate is defined by a variable, returns the definition.
    /// Otherwise, returns None.
    /// Note that this method requires iterating over all the definitions.
    fn get_def_var(&self, p: &Predicate) -> Option<&Definition> {
        self.var2def
            .iter()
            .find(|(_v, d)| &d.pred == p)
            .map(|(_v, d)| d)
    }

    /// Adds a definition.
    /// Panics if this definition is inconsistent with the existing definitions.
    /// A definition is inconsistent if the predicate is already defined by another variable.
    fn add_definition(&mut self, def: Definition) {
        let clone = def.clone();
        self.var2def
            .entry(def.var.clone())
            .and_modify(|d| {
                if d.pred != def.pred {
                    panic!("Inconsistent definitions")
                }
                match (&d.def_type, def.def_type) {
                    (DefinitionType::Negative, DefinitionType::Positive)
                    | (DefinitionType::Positive, DefinitionType::Negative) => {
                        // Was defined in other polarity, now is equivalent
                        d.def_type = DefinitionType::Equivalence
                    }
                    (_, _) => (), // nothing to do
                }
            })
            .or_insert(clone);
    }

    /// Returns an iterator over the definitions.
    pub fn iter(&self) -> impl Iterator<Item = &Definition> {
        self.var2def.values()
    }
}

pub struct Abstraction {
    /// The Boolean skeleton, a propositional formula.
    skeleton: Formula,
    /// The set of definitional Boolean variables.
    definitions: Definitions,
}

impl Abstraction {
    fn new(formula: Formula, definitions: Definitions) -> Self {
        Self {
            skeleton: formula,
            definitions,
        }
    }

    pub fn get_definitions(&self) -> &Definitions {
        &self.definitions
    }

    /// Returns the Boolean skeleton.
    pub fn get_skeleton(&self) -> &Formula {
        &self.skeleton
    }

    /// Abstracts a formula into a Boolean skeleton and a set of definitional Boolean variables.
    /// All introduced definitions are added to the definitions given as argument.
    /// The Boolean skeleton is returned.
    /// The definitions are returned as a side effect.
    ///
    /// # Panics
    /// Panics if the formula is not in NNF.
    fn abstract_fm(formula: Formula, defs: &mut Definitions, instance: &mut Instance) -> Formula {
        let res = match formula {
            Formula::Atom(Atom::Predicate(p)) => {
                let dvar = match defs.get_def_var(&p) {
                    Some(v) => v.get_var().clone(),
                    None => {
                        let v = Variable::temp(Sort::Bool);
                        instance.add_var(v.clone());
                        defs.add_definition(Definition::new(
                            v.clone(),
                            p.clone(),
                            DefinitionType::Positive,
                        ));
                        v
                    }
                };
                Formula::boolvar(dvar)
            }
            Formula::Atom(_) => formula.clone(),
            Formula::Or(fs) => {
                let fs = fs
                    .into_iter()
                    .map(|f| Self::abstract_fm(f, defs, instance))
                    .collect::<Vec<_>>();
                Formula::or(fs)
            }

            Formula::And(fs) => {
                let fs = fs
                    .into_iter()
                    .map(|f| Self::abstract_fm(f, defs, instance))
                    .collect::<Vec<_>>();
                Formula::and(fs)
            }
            Formula::Not(f) => match f.as_ref() {
                Formula::Atom(Atom::True) => Formula::ffalse(),
                Formula::Atom(Atom::False) => Formula::ttrue(),
                Formula::Atom(Atom::BoolVar(_)) => Formula::not(f.as_ref().clone()),
                Formula::Atom(Atom::Predicate(p)) => {
                    let dvar = match defs.get_def_var(p) {
                        Some(v) => v.get_var().clone(),
                        None => {
                            let v = Variable::temp(Sort::Bool);
                            instance.add_var(v.clone());
                            defs.add_definition(Definition::new(
                                v.clone(),
                                p.clone(),
                                DefinitionType::Negative,
                            ));
                            v
                        }
                    };
                    Formula::boolvar(dvar)
                }
                _ => unreachable!("Formula not in NNF"),
            },
        };
        res
    }

    /// Creates the abstraction from an instance.
    pub fn create(instance: &mut Instance) -> Result<Self, Error> {
        let mut definitions = Definitions::default();
        let skeleton = Formula::ttrue();
        Self::abstract_fm(instance.get_formula().clone(), &mut definitions, instance);
        Ok(Self::new(skeleton, definitions))
    }
}

#[cfg(test)]
mod test {

    use quickcheck_macros::quickcheck;

    use super::*;

    #[quickcheck]
    fn defintion_pos_neg_equals_equiv(p: Predicate) {
        let mut instance = Instance::default();
        let v1 = Variable::temp(Sort::Bool);
        instance.add_var(v1.clone());

        let mut defs = Definitions::default();
        defs.add_definition(Definition::new(
            v1.clone(),
            p.clone(),
            DefinitionType::Positive,
        ));
        defs.add_definition(Definition::new(v1, p.clone(), DefinitionType::Negative));
        let res = defs.get_def_var(&p).unwrap().get_def_type();
        assert_eq!(res, &DefinitionType::Equivalence);
    }

    fn is_bool(fm: &Formula) -> bool {
        match fm {
            Formula::Atom(Atom::Predicate(_)) => false,
            Formula::Atom(_) => true,
            Formula::And(fs) | Formula::Or(fs) => fs.iter().all(is_bool),
            Formula::Not(f) => is_bool(f),
        }
    }

    fn get_preds(fm: &Formula, pol: bool) -> Vec<(Predicate, bool)> {
        match fm {
            Formula::Atom(Atom::Predicate(p)) => vec![(p.clone(), pol)],
            Formula::Atom(_) => vec![],
            Formula::And(fs) | Formula::Or(fs) => fs
                .iter()
                .flat_map(|f| get_preds(f, pol))
                .collect::<Vec<_>>(),
            Formula::Not(f) => get_preds(f, !pol),
        }
    }

    #[quickcheck]
    fn abstraction_is_bool(fm: Formula) {
        let fm = fm.to_nnf();
        let mut instance = Instance::new(fm.to_nnf());
        let abstr = Abstraction::create(&mut instance);

        assert!(abstr.is_ok());
        let abstr = abstr.unwrap();
        assert!(is_bool(&abstr.skeleton));
    }

    #[quickcheck]
    fn abstraction_all_preds_defined_correctly(fm: Formula) {
        let fm = fm.to_nnf();
        let mut instance = Instance::new(fm.clone());
        let abstr = Abstraction::create(&mut instance);

        assert!(abstr.is_ok());
        let abstr = abstr.unwrap();
        let mut negs = vec![];
        let mut poss = vec![];

        for (pred, pol) in get_preds(&fm, true) {
            if pol {
                poss.push(pred);
            } else {
                negs.push(pred);
            }
        }
        for p in &negs {
            let dtype = abstr
                .get_definitions()
                .get_def_var(p)
                .unwrap()
                .get_def_type();
            if poss.contains(p) {
                assert_eq!(dtype, &DefinitionType::Equivalence)
            } else {
                assert_eq!(dtype, &DefinitionType::Negative)
            }
        }
        for p in &poss {
            let dtype = abstr
                .get_definitions()
                .get_def_var(p)
                .unwrap()
                .get_def_type();
            if negs.contains(p) {
                assert_eq!(dtype, &DefinitionType::Equivalence)
            } else {
                assert_eq!(dtype, &DefinitionType::Positive)
            }
        }
    }
}
