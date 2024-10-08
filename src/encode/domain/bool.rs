use std::rc::Rc;

use indexmap::IndexMap;

use crate::{
    context::{Context, Sort, Variable},
    ir::VarSubstitution,
    sat::{plit, pvar, PVar},
};

use super::DomainEncoding;

/// Maps Boolean variables to their corresponding PVar used in the SAT solver.
#[derive(Clone, Debug, Default)]
pub struct BoolDomain {
    var_map: IndexMap<Rc<Variable>, PVar>,
    rev_map: IndexMap<PVar, Rc<Variable>>,
}

impl BoolDomain {
    pub fn insert(&mut self, var: Rc<Variable>, pvar: PVar) {
        let ok = self.var_map.insert(var.clone(), pvar);
        assert!(ok.is_none());
        let ok = self.rev_map.insert(pvar, var);
        assert!(ok.is_none());
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<Variable>, &PVar)> {
        self.var_map.iter().map(|(var, pvar)| (var, pvar))
    }

    pub fn get(&self, var: &Rc<Variable>) -> Option<PVar> {
        self.var_map.get(var).cloned()
    }

    pub(crate) fn get_model(&self, solver: &cadical::Solver) -> VarSubstitution {
        if solver.status() != Some(true) {
            panic!("Solver is not in a SAT state")
        }
        let mut model = VarSubstitution::empty();
        for (var, v) in self.iter() {
            match solver.value(plit(*v)) {
                Some(true) => {
                    let ok = model.set_bool(var.as_ref().clone(), true);
                    assert!(ok.is_none());
                }
                Some(false) => {
                    let ok = model.set_bool(var.as_ref().clone(), false);
                    assert!(ok.is_none());
                }
                None => {
                    log::warn!("Partial model. Variable {} is not assigned", var);
                }
            }
        }
        model
    }
}

#[derive(Clone, Debug, Default)]
pub struct BoolEncoder {}
impl BoolEncoder {
    pub fn encode(&mut self, encoding: &mut DomainEncoding, ctx: &Context) {
        ctx.vars_with_sort(Sort::Bool).for_each(|var| {
            if encoding.bool.get(var).is_none() {
                let pvar = pvar();
                encoding.bool.insert(var.clone(), pvar);
            }
        });
    }
}
