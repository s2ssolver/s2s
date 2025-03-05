use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};
use regulaer::{automaton::NFA, re::Regex};

use crate::{
    interval::Interval,
    node::{NodeManager, Variable},
};

use super::{Bounds, InferringStrategy};

type InRe = (Rc<Variable>, Regex, bool);
type VarEq = (Rc<Variable>, Rc<Variable>);

#[derive(Debug, Clone, Default)]
pub(super) struct RegularBoundsInferer {
    // Literals of the form `x \in R` or `x \notin R`.
    regs: IndexSet<InRe>,

    // Literals of the form `x = y`
    eqs: IndexSet<VarEq>,
    // Literals of the form `x != y`
    neqs: IndexSet<VarEq>,

    /// The intersection of all automata for each variable.
    /// The NFAs are wrapped in an RC to make cloning cheap.
    intersections: IndexMap<Rc<Variable>, Rc<NFA>>,

    conflict: bool,
}

impl RegularBoundsInferer {
    pub fn add_reg(
        &mut self,
        var: Rc<Variable>,
        re: Regex,
        polarity: bool,
        mngr: &mut NodeManager,
    ) {
        // cloning the regex is cheap, it is an Rc.
        self.regs.insert((var.clone(), re.clone(), polarity));
        if !self.conflict {
            // Update the intersection automaton.
            let re_pol = if polarity {
                re
            } else {
                mngr.re_builder().comp(re)
            };
            let nfa = mngr.get_nfa(&re_pol);
            // TODO: Cache intersection, they are likely to be used in other inferrence steps too.
            match self.intersections.entry(var) {
                indexmap::map::Entry::Occupied(o) => {
                    let mut inter = o.get().intersect(&nfa).unwrap();
                    inter.trim();
                    if inter.is_empty() {
                        self.conflict = true;
                    }
                    *o.into_mut() = Rc::new(inter);
                }
                indexmap::map::Entry::Vacant(v) => {
                    v.insert(nfa);
                }
            }
        }
    }

    pub fn add_const_eq(
        &mut self,
        var: Rc<Variable>,
        word: String,
        pol: bool,
        mngr: &mut NodeManager,
    ) {
        let builder = mngr.re_builder();
        let re = builder.word(word.into());
        self.add_reg(var, re, pol, mngr);
    }

    pub fn add_var_eq(&mut self, x: Rc<Variable>, y: Rc<Variable>, polarity: bool) {
        if polarity {
            // For all existing reg constraints `v \in R`, replace `v` with `x` if `v == y`.
            let mut new_regs = IndexSet::new();
            for (v, r, p) in std::mem::take(&mut self.regs).into_iter() {
                if v == y {
                    new_regs.insert((x.clone(), r, p));
                } else {
                    new_regs.insert((v, r, p));
                }
            }
            self.regs = new_regs;

            // For all existing eq constraints `v1 = v2`, replace `v2` with `x` if `v2 == y`.
            let mut new_neqs = IndexSet::new();
            for (v1, v2) in std::mem::take(&mut self.neqs).into_iter() {
                if v2 == y {
                    new_neqs.insert((v1.clone(), x.clone()));
                } else {
                    new_neqs.insert((v1.clone(), v2.clone()));
                }
            }
            self.neqs = new_neqs;

            // Update the intersection automata
            let mut new_intersections = IndexMap::new();
            for (v, nfa) in std::mem::take(&mut self.intersections).into_iter() {
                if v == y {
                    new_intersections.insert(x.clone(), nfa.clone());
                } else {
                    new_intersections.insert(v.clone(), nfa.clone());
                }
            }
            self.intersections = new_intersections;

            self.eqs.insert((x.clone(), y.clone()));
        } else {
            if x == y {
                // This is trivially contradictory.
                self.conflict = true;
            }
            self.neqs.insert((x, y));
        }
    }

    /// Returns the partition of non-equality literals.
    /// Returns a vector of equivalence classes such that all variables in the same class must not be equal.
    /// In other words, two variables are in the same class iff
    /// - there is a x
    fn partition_neqs(&self) -> Vec<Vec<Rc<Variable>>> {
        let egdes = self
            .neqs
            .iter()
            .map(|(x, y)| (x.clone(), y.clone()))
            .collect::<Vec<_>>();

        let mut nodes = self.neqs.iter().fold(IndexSet::new(), |mut set, (x, y)| {
            set.insert(x.clone());
            set.insert(y.clone());
            set
        });

        let mut adj = IndexMap::new();
        for (x, y) in egdes {
            adj.entry(x.clone())
                .or_insert_with(IndexSet::new)
                .insert(y.clone());
            adj.entry(y.clone())
                .or_insert_with(IndexSet::new)
                .insert(x.clone());
        }

        let mut components = Vec::new();
        while !nodes.is_empty() {
            let mut comp = Vec::new();
            let mut stack = vec![nodes.iter().next().unwrap().clone()];
            while let Some(node) = stack.pop() {
                comp.push(node.clone());
                nodes.remove(&node);
                for neigh in adj.get(&node).unwrap_or(&IndexSet::new()) {
                    if nodes.contains(neigh) {
                        stack.push(neigh.clone());
                    }
                }
            }
            components.push(comp);
        }

        components
    }

    pub fn iter_intersections(&self) -> impl Iterator<Item = (&Rc<Variable>, &Rc<NFA>)> {
        self.intersections.iter()
    }
}

impl InferringStrategy for RegularBoundsInferer {
    fn infer(&mut self) -> Option<Bounds> {
        if self.conflict {
            return None;
        }
        // For each variable, use the number of states in the intersection automaton as the upper bound.
        let mut bounds = Bounds::default();
        for (v, nfa) in self.intersections.iter() {
            if nfa.is_empty() {
                self.conflict = true;
                return None;
            }
            let upper = nfa.num_states().saturating_sub(1);
            let lower = nfa.shortest().unwrap_or(0);
            // TODO: use shortest path to find lower bound.
            bounds.set(v.clone(), Interval::new(lower, upper));
        }

        // Adjust based on the non-equality constraints.

        let components = self.partition_neqs();
        for component in components.into_iter() {
            // multiply all upper bounds of the variables in the component.
            let mut prod: Option<isize> = Some(1);
            // todo: let lower equalt to minimum(?) of all lower bounds.
            for var in &component {
                if let Some(bounds_v) = bounds.get(var) {
                    if let Some(upper) = bounds_v.upper_finite() {
                        prod = prod
                            .and_then(|p| p.checked_mul(upper as isize))
                            .and_then(|p| p.checked_mul(2));
                    } else {
                        // Is infinite, so the product is infinite.
                        prod = None;
                    }
                }
                // Otherwise the variable is not constrained by any regular constraint.
            }
            for var in &component {
                match prod {
                    Some(prod) => {
                        bounds.set(var.clone(), Interval::new(0, prod));
                    }
                    None => {
                        bounds.set(var.clone(), Interval::bounded_below(0));
                    }
                }
            }
        }
        // Undo the substitutions.
        for (x, y) in self.eqs.iter() {
            if let Some(bound) = bounds.get(x) {
                bounds.set(y.clone(), bound);
            }
        }

        Some(bounds)
    }

    fn conflict(&self) -> bool {
        self.conflict
    }
}

#[cfg(test)]
mod tests {
    use crate::node::Sort;

    use super::*;

    #[test]
    fn test_infer_single_re_finite() {
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re = regulaer::parse::parse_rust("^aa$", rebuilder, true).unwrap();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re, true, &mut mngr);

        let bounds = inferer.infer().unwrap();
        assert_eq!(bounds.get(&v), Some(Interval::new(2, 2)));
    }

    #[test]
    fn test_infer_single_re_star() {
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re = regulaer::parse::parse_rust("^(aa)*$", rebuilder, true).unwrap();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re, true, &mut mngr);

        let bounds = inferer.infer().unwrap();
        assert_eq!(bounds.get(&v), Some(Interval::new(0, 2)));
    }

    #[test]
    fn test_infer_intersection() {
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re1 = regulaer::parse::parse_rust("^(aa)*$", rebuilder, true).unwrap();
        let re2 = regulaer::parse::parse_rust("^(aaa)*$", rebuilder, true).unwrap();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re1, true, &mut mngr);
        inferer.add_reg(v.clone(), re2, true, &mut mngr);

        let bounds = inferer.infer().unwrap();

        assert_eq!(bounds.get(&v), Some(Interval::new(0, 6)));
    }

    #[test]
    fn test_infer_intersection_comp() {
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re1 = regulaer::parse::parse_rust("^(aaa)*$", rebuilder, true).unwrap();
        let re2 = regulaer::parse::parse_rust("^aaa$", rebuilder, true).unwrap();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re1, true, &mut mngr);
        inferer.add_reg(v.clone(), re2, false, &mut mngr);

        let bounds = inferer.infer().unwrap();

        assert_eq!(bounds.get(&v), Some(Interval::new(0, 6)));
    }

    #[test]
    fn test_infer_intersection_comp_2() {
        // (aaa)* and not(aaa) and not epsilon ==> smallest is aaaaaa, upper bound is 6
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re1 = regulaer::parse::parse_rust("^(aaa)*$", rebuilder, true).unwrap();
        let re2 = regulaer::parse::parse_rust("^aaa$", rebuilder, true).unwrap();
        let epsi = rebuilder.epsilon();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re1, true, &mut mngr);
        inferer.add_reg(v.clone(), re2, false, &mut mngr);
        inferer.add_reg(v.clone(), epsi, false, &mut mngr);

        let bounds = inferer.infer().unwrap();
        assert_eq!(bounds.get(&v), Some(Interval::new(6, 6)));
    }

    #[test]
    fn test_infer_intersection_empty() {
        let mut mngr = NodeManager::default();
        let rebuilder = mngr.re_builder();
        let re1 = regulaer::parse::parse_rust("^aaaa$", rebuilder, true).unwrap();
        let re2 = regulaer::parse::parse_rust("^(aa)*$", rebuilder, true).unwrap();
        let v = mngr.temp_var(Sort::String);

        let mut inferer = RegularBoundsInferer::default();
        inferer.add_reg(v.clone(), re1, true, &mut mngr);
        inferer.add_reg(v.clone(), re2, false, &mut mngr);

        let bounds = inferer.infer();

        assert!(inferer.conflict);
        assert_eq!(bounds, None);
    }
}
