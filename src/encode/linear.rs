use std::collections::VecDeque;

use indexmap::{IndexMap, IndexSet};

use crate::{
    model::{linears::LinearConstraint, Sort, Variable},
    sat::{as_lit, neg, pvar, PVar},
};

use super::{EncodingResult, IntegerDomainBounds, PredicateEncoder};

/// Encodes linear constraints by using multi-valued decision diagrams.
pub struct MddEncoder {
    linear: LinearConstraint,

    nodes: IndexMap<usize, IndexMap<isize, PVar>>,

    mdd_root: PVar,
    mdd_false: PVar,
    mdd_true: PVar,

    last_bounds: Option<IntegerDomainBounds>,
}

impl MddEncoder {
    pub fn new(linear: LinearConstraint) -> Self {
        let root_pvar = pvar();
        let mut node_map = IndexMap::new();
        let mut root_node_vals = IndexMap::new();
        root_node_vals.insert(0, root_pvar);

        node_map.insert(0, root_node_vals);
        Self {
            linear,
            nodes: node_map,
            mdd_false: pvar(),
            mdd_true: pvar(),
            mdd_root: root_pvar,
            last_bounds: None,
        }
    }

    fn last_bound(&self, var: &Variable) -> isize {
        let v = if var.sort() == Sort::String {
            var.len_var()
        } else {
            var.clone()
        };
        self.last_bounds
            .as_ref()
            .map(|b| b.get_upper(&v))
            .unwrap_or(0)
    }
}

impl PredicateEncoder for MddEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &super::IntegerDomainBounds,
        dom: &super::domain::DomainEncoding,
        var_manager: &crate::model::VarManager,
    ) -> super::EncodingResult {
        let mut res = EncodingResult::empty();

        let mut queue = VecDeque::new();
        // (level, value, pvar)
        queue.push_back((0, 0, self.mdd_root));

        while let Some((level, value, node_var)) = queue.pop_front() {
            match &self.linear.lhs()[level] {
                crate::model::linears::LinearArithFactor::VarCoeff(v, coeff) => {
                    let last_bound = match self.last_bound(v) {
                        0 => 0,
                        b => b + 1,
                    };

                    let current_bound = bounds.get_upper(v);
                    for l in last_bound..=current_bound {
                        let len_assign_var = dom.int().get(&v, l).unwrap();
                        let new_value = value + l * coeff;
                        if level + 1 < self.linear.lhs.len() {
                            let child_pvar = *self
                                .nodes
                                .entry(level + 1)
                                .or_default()
                                .entry(new_value)
                                .or_insert_with(|| pvar());
                            res.add_clause(vec![
                                neg(node_var),
                                neg(len_assign_var),
                                as_lit(child_pvar),
                            ]);

                            queue.push_back((level + 1, new_value, child_pvar));
                        } else {
                            let node = match self.linear.typ {
                                crate::model::linears::LinearConstraintType::Eq => {
                                    if new_value == self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                crate::model::linears::LinearConstraintType::Leq => {
                                    if new_value <= self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                crate::model::linears::LinearConstraintType::Less => {
                                    if new_value < self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                crate::model::linears::LinearConstraintType::Geq => {
                                    if new_value >= self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                crate::model::linears::LinearConstraintType::Greater => {
                                    if new_value > self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                            };
                            res.add_clause(vec![neg(node_var), neg(len_assign_var), as_lit(node)]);
                        }
                    }
                }
                crate::model::linears::LinearArithFactor::Const(_) => {
                    todo!("Consts not supported: {}", self.linear)
                }
            }
        }
        res.add_clause(vec![as_lit(self.mdd_root)]);
        res.add_clause(vec![neg(self.mdd_false)]);
        res
    }
}
