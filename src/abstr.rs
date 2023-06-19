//! The abstraction module. Provide functions to abstract formulas into a Boolean skeleton and a set of definitional Boolean variables.

use indexmap::IndexMap;

use crate::{
    error::Error,
    model::{
        formula::{Formula, Predicate},
        Sort, VarManager, Variable,
    },
    parse::Instance,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Defined {
    /// A definition of the form `p <=> f`.
    Equivalence(Predicate),
    /// A definition of the form `p => f`.
    ImplicationPos(Predicate),
    /// A definition of the form `!p => !f`.
    ImplicationNeg(Predicate),
}

#[derive(Debug, Default)]
struct Definitions {
    var2def: IndexMap<Variable, Defined>,
    def2var: IndexMap<Defined, Variable>,
}

impl Definitions {
    fn get_def_var(&self, def: &Defined) -> Option<&Variable> {
        self.def2var.get(def)
    }

    fn get_defined(&self, var: &Variable) -> Option<&Defined> {
        self.var2def.get(var)
    }

    fn set_def_var(&mut self, var: &Variable, def: &Defined) {
        match def {
            Defined::Equivalence(_) => {
                self.def2var.insert(def.clone(), var.clone());
                self.var2def.insert(var.clone(), def.clone());
            }
            Defined::ImplicationPos(p) => {
                if let Some(Defined::ImplicationNeg(p2)) = self.var2def.get(var) {
                    debug_assert!(p == p2);
                    self.var2def
                        .insert(var.clone(), Defined::Equivalence(p.clone()));
                    self.def2var
                        .insert(Defined::Equivalence(p.clone()), var.clone());
                } else {
                    self.var2def.insert(var.clone(), def.clone());
                    self.def2var.insert(def.clone(), var.clone());
                }
            }
            Defined::ImplicationNeg(p) => {
                if let Some(Defined::ImplicationPos(p2)) = self.var2def.get(var) {
                    debug_assert!(p == p2);
                    self.var2def
                        .insert(var.clone(), Defined::Equivalence(p.clone()));
                    self.def2var
                        .insert(Defined::Equivalence(p.clone()), var.clone());
                } else {
                    self.var2def.insert(var.clone(), def.clone());
                    self.def2var.insert(def.clone(), var.clone());
                }
            }
        }
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
            definitions: definitions,
        }
    }

    pub fn get_defined(&self, var: &Variable) -> Option<&Defined> {
        self.definitions.get_defined(var)
    }

    pub fn get_def_var(&self, def: &Defined) -> Option<&Variable> {
        self.definitions.get_def_var(def)
    }

    /// Abstracts a formula into a Boolean skeleton and a set of definitional Boolean variables.
    fn abstract_fm(
        formula: Formula,
        defs: &mut Definitions,
        var_manager: &mut VarManager,
    ) -> Formula {
        let res = match formula {
            Formula::True | Formula::False | Formula::BoolVar(_) => formula.clone(),
            Formula::Or(fs) => {
                let mut fs = fs
                    .into_iter()
                    .map(|f| Self::abstract_fm(f, defs, var_manager))
                    .collect::<Vec<_>>();
                Formula::or(fs)
            }
            Formula::Predicate(p) => {
                let dvar = match defs.get_def_var(&Defined::Equivalence(p.clone())) {
                    Some(v) => v.clone(),
                    None => match defs.get_def_var(&Defined::ImplicationPos(p.clone())) {
                        Some(v) => v.clone(),
                        None => {
                            let v = var_manager.tmp_var(Sort::Bool);
                            defs.set_def_var(&v, &Defined::ImplicationPos(p));
                            v
                        }
                    },
                };
                Formula::BoolVar(dvar)
            }
            Formula::And(fs) => {
                let fs = fs
                    .into_iter()
                    .map(|f| Self::abstract_fm(f, defs, var_manager))
                    .collect::<Vec<_>>();
                Formula::and(fs)
            }
            Formula::Not(f) => match f.as_ref() {
                Formula::True => Formula::False,
                Formula::False => Formula::True,
                Formula::BoolVar(_) => Formula::not(f.as_ref().clone()),
                Formula::Predicate(p) => {
                    let dvar = match defs.get_def_var(&Defined::Equivalence(p.clone())) {
                        Some(v) => v.clone(),
                        None => match defs.get_def_var(&Defined::ImplicationNeg(p.clone())) {
                            Some(v) => v.clone(),
                            None => {
                                let v = var_manager.tmp_var(Sort::Bool);
                                defs.set_def_var(&v, &Defined::ImplicationNeg(p.clone()));
                                v
                            }
                        },
                    };
                    Formula::BoolVar(dvar)
                }
                _ => unreachable!("Formula not in NNF"),
            },
        };
        res
    }

    pub fn create(instance: &mut Instance) -> Result<Self, Error> {
        let mut definitions = Definitions::default();
        let skeleton = Formula::ttrue();
        Self::abstract_fm(
            instance.get_formula().clone(),
            &mut definitions,
            instance.get_var_manager_mut(),
        );
        Ok(Self::new(skeleton, definitions))
    }
}

#[cfg(test)]
mod test {

    use quickcheck_macros::quickcheck;

    use super::*;

    fn is_bool(fm: &Formula) -> bool {
        match fm {
            Formula::True | Formula::False | Formula::BoolVar(_) => true,
            Formula::Predicate(_) => false,
            Formula::And(fs) | Formula::Or(fs) => fs.iter().all(|f| is_bool(f)),
            Formula::Not(f) => is_bool(f),
        }
    }

    fn get_preds(fm: &Formula, pol: bool) -> Vec<(Predicate, bool)> {
        match fm {
            Formula::True | Formula::False | Formula::BoolVar(_) => vec![],
            Formula::Predicate(p) => vec![(p.clone(), pol)],
            Formula::And(fs) | Formula::Or(fs) => fs
                .iter()
                .map(|f| get_preds(f, pol))
                .flatten()
                .collect::<Vec<_>>(),
            Formula::Not(f) => get_preds(f, !pol),
        }
    }

    #[quickcheck]
    fn abstraction_is_bool(fm: Formula) {
        let fm = fm.to_nnf();
        let mut instance = Instance::new(fm.clone(), VarManager::new());
        let abstr = Abstraction::create(&mut instance);

        assert!(abstr.is_ok());
        let abstr = abstr.unwrap();
        assert!(is_bool(&abstr.skeleton));
    }

    #[quickcheck]
    fn abstraction_all_preds_defined_correctly(fm: Formula) {
        let fm = fm.to_nnf();
        let mut instance = Instance::new(fm.clone(), VarManager::new());
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
            if poss.contains(p) {
                assert!(abstr
                    .get_def_var(&Defined::Equivalence(p.clone()))
                    .is_some())
            } else {
                assert!(abstr
                    .get_def_var(&Defined::ImplicationNeg(p.clone()))
                    .is_some())
            }
        }
        for p in &poss {
            if negs.contains(p) {
                assert!(abstr
                    .get_def_var(&Defined::Equivalence(p.clone()))
                    .is_some())
            } else {
                assert!(abstr
                    .get_def_var(&Defined::ImplicationPos(p.clone()))
                    .is_some())
            }
        }
    }
}
