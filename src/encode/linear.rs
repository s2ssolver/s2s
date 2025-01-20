use std::collections::VecDeque;

use indexmap::IndexMap;

use crate::{
    bounds::Bounds,
    node::{
        canonical::{ArithOperator, LinearConstraint, LinearSummand},
        Sorted,
    },
    sat::{nlit, plit, pvar, PVar},
};

use super::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder};

/// Encodes linear constraints by using multi-valued decision diagrams.
pub struct MddEncoder {
    linear: LinearConstraint,

    nodes: IndexMap<usize, IndexMap<i64, PVar>>,

    mdd_root: PVar,
    mdd_false: PVar,
    mdd_true: PVar,

    /// The current round of encoding (starting at 1). Used to avoid encoding the same constraint multiple times.
    /// Is 0 when the encoder is reset.
    round: usize,

    last_bounds: Option<Bounds>,
}

impl MddEncoder {
    pub fn new(linear: LinearConstraint, pol: bool) -> Self {
        let mut linear = if pol { linear } else { linear.negate() };
        linear.canonicalize();
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
}

impl LiteralEncoder for MddEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        self.round += 1;

        let mut res = EncodingResult::empty();

        let mut queue = VecDeque::new();
        // (level, value, pvar)
        queue.push_back((0, 0, self.mdd_root));

        while let Some((level, value, node_var)) = queue.pop_front() {
            match &self.linear.lhs()[level] {
                LinearSummand::Mult(var, coeff) => {
                    let v = var.variable();
                    let current_u_bound =
                        bounds.get_upper_finite(v).expect("Unbounded variable") as i64;
                    let current_l_bound =
                        bounds.get_lower_finite(v).expect("Unbounded variable") as i64;

                    for l in current_l_bound..=current_u_bound {
                        if let Some(last_bounds) = self.last_bounds.as_ref() {
                            if last_bounds
                                .get_lower_finite(v)
                                .map(|ll| l >= ll as i64)
                                .unwrap_or(false)
                                && last_bounds
                                    .get_upper_finite(v)
                                    .map(|uu| l <= uu as i64)
                                    .unwrap_or(false)
                            {
                                // Already encoded
                                continue;
                            }
                        }
                        // If string: get length encoding, if int: get int encoding
                        let len_assign_var = if v.sort().is_int() {
                            dom.int().get(v, l).unwrap()
                        } else {
                            dom.string().get_len(v, l as usize).unwrap()
                        };
                        let new_value = value + l * coeff;
                        if level + 1 < self.linear.lhs().len() {
                            let child_pvar = *self
                                .nodes
                                .entry(level + 1)
                                .or_default()
                                .entry(new_value)
                                .or_insert_with(pvar);
                            res.add_clause(vec![
                                nlit(node_var),
                                nlit(len_assign_var),
                                plit(child_pvar),
                            ]);

                            queue.push_back((level + 1, new_value, child_pvar));
                        } else {
                            let node = match self.linear.operator() {
                                ArithOperator::Eq => {
                                    if new_value == self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                ArithOperator::Ineq => {
                                    if new_value != self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                ArithOperator::Leq => {
                                    if new_value <= self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                ArithOperator::Less => {
                                    if new_value < self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                ArithOperator::Geq => {
                                    if new_value >= self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                                ArithOperator::Greater => {
                                    if new_value > self.linear.rhs() {
                                        self.mdd_true
                                    } else {
                                        self.mdd_false
                                    }
                                }
                            };
                            res.add_clause(vec![nlit(node_var), nlit(len_assign_var), plit(node)]);
                        }
                    }
                }
                LinearSummand::Const(_) => {
                    todo!("Consts not supported: {}", self.linear)
                }
            }
        }
        if self.round == 1 {
            res.add_clause(vec![plit(self.mdd_root)]);
            res.add_clause(vec![nlit(self.mdd_false)]);
        }
        // TODO: This leads to soundness errors, need to investigate!
        //self.last_bounds = Some(bounds.clone());
        Ok(res)
    }
}

// TODO: Needs to be tested
