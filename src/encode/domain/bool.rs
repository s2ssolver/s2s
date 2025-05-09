use std::rc::Rc;

use indexmap::IndexMap;
use rustsat::solvers::Solve;
use rustsat_cadical::CaDiCaL;

use crate::{
    ast::VarSubstitution,
    context::{Context, Variable},
    domain::Domain,
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
        self.var_map.iter()
    }

    pub fn get(&self, var: &Rc<Variable>) -> Option<PVar> {
        self.var_map.get(var).cloned()
    }

    pub(crate) fn get_model(&self, solver: &CaDiCaL, ctx: &mut Context) -> VarSubstitution {
        let mut model = VarSubstitution::default();
        let sol = solver.full_solution().expect("No solution found");
        for (var, v) in self.iter() {
            if sol.lit_value(plit(*v)).to_bool_with_def(false) {
                model.add(var.clone(), ctx.ast().ttrue());
            } else {
                model.add(var.clone(), ctx.ast().ffalse());
            }
        }
        model
    }
}

#[derive(Clone, Debug, Default)]
pub struct BoolEncoder {}
impl BoolEncoder {
    pub fn encode(&mut self, encoding: &mut DomainEncoding, dom: &Domain) {
        dom.iter_bool().for_each(|var| {
            if encoding.bool.get(var).is_none() {
                let pvar = pvar();
                encoding.bool.insert(var.clone(), pvar);
            }
        });
    }
}
