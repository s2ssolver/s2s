//! Performs static analysis on the formula by assigning a truth value to Boolean variables and simplifying under that assumptions.

use std::{collections::VecDeque, rc::Rc};

use indexmap::IndexSet;

use crate::{
    node::{Node, NodeKind, NodeManager, Sorted, VarSubstitution, Variable},
    SolverOptions,
};

use super::simp::{SimpResult, Simplifier};

pub(super) struct BoolVarGuesser {
    options: SolverOptions,
}

impl BoolVarGuesser {
    pub fn new(options: SolverOptions) -> Self {
        Self { options }
    }

    pub fn apply(self, fm: &Node, mngr: &mut NodeManager) -> SimpResult {
        let mut res = fm.clone();
        let mut subs = Vec::new();

        while let Some(inferred) = self.pass(&res, mngr) {
            res = inferred.node;
            for s in inferred.subs {
                subs.push(s);
            }
        }
        SimpResult { node: res, subs }
    }

    fn pass(&self, fm: &Node, mngr: &mut NodeManager) -> Option<SimpResult> {
        // Collect the Boolean variables
        let bavrs = self.collect_bool_vars(fm);

        for v in bavrs {
            let vals = vec![true, false];
            for truth_val in vals {
                // create a substitution mapping this var to `true` and apply it to the formula
                let mut sub = VarSubstitution::default();
                let bool_const = if truth_val {
                    mngr.ttrue()
                } else {
                    mngr.ffalse()
                };
                sub.add(v.clone(), bool_const);
                let fm_v_true = sub.apply(fm, mngr);
                // try to simp
                let mut simped = self.simp(&fm_v_true, mngr);
                if let Some(res) = simped.node.as_bool_const() {
                    if res {
                        log::debug!("Setting {v} to `{truth_val}` short-circuits the formula");
                        // Formula is true, this v is a backdoor variable
                        simped.subs.insert(0, sub);
                        return Some(simped);
                    } else {
                        // Formula is false if v is `truth_val`, we must assert the opposite
                        log::debug!("Setting {v} to `{truth_val}` cannot satisfy the formula");
                        let vnode = mngr.var(v);
                        let opposite = if truth_val { mngr.not(vnode) } else { vnode };
                        let new_node = mngr.and(vec![fm.clone(), opposite]);
                        // Simplify again now with the knowledge of the value of v
                        return Some(self.simp(&new_node, mngr));
                    }
                }
            }
        }
        None
    }

    /// Collects all Boolean variables in the formula.
    /// The higher the level the earlier the index in the resulting vector
    fn collect_bool_vars(&self, fm: &Node) -> Vec<Rc<Variable>> {
        let mut seen = IndexSet::new();
        let mut queue = VecDeque::new();
        let mut res = Vec::new();
        queue.push_back(fm);
        seen.insert(fm);

        while let Some(node) = queue.pop_front() {
            if let NodeKind::Variable(v) = node.kind() {
                if v.sort().is_bool() {
                    res.push(v.clone())
                }
            } else {
                for n in node.children() {
                    if seen.insert(n) {
                        queue.push_front(n);
                    }
                }
            }
        }

        res
    }

    fn simp(&self, fm: &Node, mngr: &mut NodeManager) -> SimpResult {
        let simper = Simplifier::default();
        simper.apply(fm, self.options.simp_max_passes, mngr)
    }
}
