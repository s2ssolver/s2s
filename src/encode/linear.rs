use std::collections::VecDeque;

use indexmap::IndexMap;

use crate::{
    bounds::Bounds,
    model::{
        constraints::{LinearArithFactor, LinearConstraint, LinearConstraintType},
        Evaluable, Sort, Substitution, Variable,
    },
    sat::{as_lit, neg, pvar, PVar},
};

use super::{ConstraintEncoder, EncodingResult};

/// Encodes linear constraints by using multi-valued decision diagrams.
pub struct MddEncoder {
    linear: LinearConstraint,

    nodes: IndexMap<usize, IndexMap<isize, PVar>>,

    mdd_root: PVar,
    mdd_false: PVar,
    mdd_true: PVar,

    /// The current round of encoding (starting at 1). Used to avoid encoding the same constraint multiple times.
    /// Is 0 when the encoder is reset.
    round: usize,

    last_bounds: Option<Bounds>,
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
            round: 0,
            last_bounds: None,
        }
    }

    fn last_bound(&self, var: &Variable) -> isize {
        let v = if var.sort() == Sort::String {
            var.len_var().unwrap()
        } else {
            var.clone()
        };
        self.last_bounds
            .as_ref()
            .map(|b| b.get_upper(&v).unwrap_or(0))
            .unwrap_or(0)
    }
}

impl ConstraintEncoder for MddEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        dom: &super::domain::DomainEncoding,
    ) -> super::EncodingResult {
        self.round += 1;
        let mut res = EncodingResult::empty();

        // Check if trivial
        match self.linear.eval(&Substitution::new()) {
            Some(true) => return res,
            Some(false) => {
                res.add_clause(vec![neg(self.mdd_root), as_lit(self.mdd_false)]);
                return res;
            }
            None => {}
        }

        let mut queue = VecDeque::new();
        // (level, value, pvar)
        queue.push_back((0, 0, self.mdd_root));

        while let Some((level, value, node_var)) = queue.pop_front() {
            match &self.linear.lhs()[level] {
                LinearArithFactor::VarCoeff(v, coeff) => {
                    let last_bound = match self.last_bound(v) {
                        0 => 0,
                        b => b + 1,
                    };

                    let current_bound = bounds.get_upper(v).expect("Unbounded variable");
                    for l in last_bound..=current_bound {
                        let len_assign_var = dom.int().get(v, l).unwrap();
                        let new_value = value + l * coeff;
                        if level + 1 < self.linear.lhs.len() {
                            let child_pvar = *self
                                .nodes
                                .entry(level + 1)
                                .or_default()
                                .entry(new_value)
                                .or_insert_with(pvar);
                            res.add_clause(vec![
                                neg(node_var),
                                neg(len_assign_var),
                                as_lit(child_pvar),
                            ]);

                            queue.push_back((level + 1, new_value, child_pvar));
                        } else {
                            let node = match self.linear.typ {
                                LinearConstraintType::Eq => {
                                    if new_value == self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                LinearConstraintType::Leq => {
                                    if new_value <= self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                LinearConstraintType::Less => {
                                    if new_value < self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                LinearConstraintType::Geq => {
                                    if new_value >= self.linear.rhs {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                LinearConstraintType::Greater => {
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
                LinearArithFactor::Const(_) => {
                    todo!("Consts not supported: {}", self.linear)
                }
            }
        }
        if self.round == 1 {
            res.add_clause(vec![as_lit(self.mdd_root)]);
            res.add_clause(vec![neg(self.mdd_false)]);
        }
        res
    }
}
