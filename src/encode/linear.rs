use std::{cell::RefCell, collections::VecDeque, hash::Hash, rc::Rc};

use indexmap::{IndexMap, IndexSet};
use rustsat::types::Clause;

use crate::context::*;
use crate::{
    domain::Domain,
    ir::{LIAConstraint, LIAOp, Monomial},
    sat::{nlit, plit, pvar, PVar},
};

use super::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink};

/// Encodes linear constraints by using multi-valued decision diagrams.
pub struct MddEncoder {
    linear: LIAConstraint,

    /// The current round of encoding (starting at 1). Used to avoid encoding the same constraint multiple times.
    /// Is 0 when the encoder is reset.
    round: usize,

    last_bounds: Option<Domain>,

    nodes: IndexMap<usize, IndexMap<i64, Rc<RefCell<MddNode>>>>,
}

impl MddEncoder {
    pub fn new(linear: LIAConstraint, pol: bool) -> Self {
        let mut linear = if pol { linear } else { linear.negate() };
        linear.canonicalize();

        let root = MddNode::new(0, 0);
        let root_ref = Rc::new(RefCell::new(root));

        let mut l0_nodes = IndexMap::new();
        l0_nodes.insert(0i64, root_ref);

        let mut nodes = IndexMap::new();
        nodes.insert(0usize, l0_nodes);
        Self {
            linear,
            nodes,
            round: 0,
            last_bounds: None,
        }
    }

    /// Checks if from the given node we can reach a solution node.
    fn feasible(&self, node: &MddNode, dom: &Domain) -> bool {
        // Check the values we can reach from this partial sum
        let mut min = node.value;
        let mut max = node.value;
        for lev in node.level..self.linear.lhs().len() {
            match &self.linear.lhs()[lev] {
                Monomial::Mult(v, coeff) => {
                    let bound = if v.is_int() {
                        dom.get_int(v.variable())
                    } else {
                        dom.get_string(v.variable())
                    }
                    .expect("Unbounded variable");
                    let upper = bound.upper_finite().expect("Unbounded variable") as i64;
                    let lower = bound.lower_finite().expect("Unbounded variable") as i64;
                    let lo = coeff * lower;
                    let hi = coeff * upper;
                    // change if we have a negative coeff
                    let (lo, hi) = if lo > hi { (hi, lo) } else { (lo, hi) };
                    min += lo;
                    max += hi;
                }
                Monomial::Const(_) => unreachable!(),
            }
        }
        let rhs = self.linear.rhs();

        match self.linear.operator() {
            LIAOp::Eq => min <= rhs && rhs <= max,
            LIAOp::Ineq => !(min == rhs && max == rhs),
            LIAOp::Leq => min <= rhs,
            LIAOp::Less => min < rhs,
            LIAOp::Geq => max >= rhs,
            LIAOp::Greater => max > rhs,
        }
    }

    /// Checks if the given partial sum is a solution to the linear constraint.
    fn is_solution(&self, val: i64) -> bool {
        let rhs = self.linear.rhs();

        match self.linear.operator() {
            LIAOp::Eq => val == rhs,
            LIAOp::Ineq => val != rhs,
            LIAOp::Leq => val <= rhs,
            LIAOp::Less => val < rhs,
            LIAOp::Geq => val >= rhs,
            LIAOp::Greater => val > rhs,
        }
    }
}

impl EncodeLiteral for MddEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        self.round += 1;
        let mut queue = VecDeque::new();
        // (level, value, pvar)

        let root = self.nodes[0][0].clone();
        let root_var = root.borrow().bool_var;
        queue.push_back(root);
        let mut seen = IndexSet::new();
        // (level, psum)
        seen.insert((0, 0));

        while let Some(node) = queue.pop_front() {
            let level = node.borrow().level;
            let psum = node.borrow().value;
            let node_var = node.borrow().bool_var;

            match &self.linear.lhs()[level] {
                Monomial::Mult(var, coeff) => {
                    let v = var.variable();
                    let current_bound = if v.sort().is_string() {
                        dom.get_string(v)
                    } else if v.sort().is_int() {
                        dom.get_int(v)
                    } else {
                        unreachable!()
                    };

                    let current_u_bound = current_bound
                        .and_then(|i| i.upper_finite())
                        .expect("Unbounded variable")
                        as i64;
                    let current_l_bound = current_bound
                        .and_then(|i| i.lower_finite())
                        .expect("Unbounded variable")
                        as i64;

                    let (old_lo, old_hi) = if let Some((old_lo, old_hi)) = node.borrow().lo_hi {
                        (old_lo, old_hi)
                    } else {
                        (1, 0)
                    };

                    for l in current_l_bound..=current_u_bound {
                        let new_psum = psum + l * coeff; // the partial sum we end up with if we take this value

                        // If string: get length encoding, if int: get int encoding
                        let len_assign_var = if v.sort().is_int() {
                            dom_enc.int().get(v, l).unwrap()
                        } else {
                            dom_enc.string().get_len(v, l as usize).unwrap()
                        };
                        if level + 1 < self.linear.lhs().len() {
                            let nodes_in_level = self.nodes.entry(level + 1).or_default();
                            // Check if we have already seen this node
                            let child = match nodes_in_level.entry(new_psum) {
                                indexmap::map::Entry::Occupied(c) => c.get().clone(),
                                indexmap::map::Entry::Vacant(v) => {
                                    // If we have not seen this node, we create it
                                    let new_node = MddNode::new(level + 1, new_psum);
                                    let new_child = Rc::new(RefCell::new(new_node));

                                    v.insert(new_child.clone());

                                    new_child
                                }
                            };

                            let child_pvar = child.borrow().bool_var;

                            if l < old_lo || old_hi < l {
                                sink.add_clause(Clause::from([
                                    nlit(node_var),
                                    nlit(len_assign_var),
                                    plit(child_pvar),
                                ]));
                            }

                            if self.feasible(&child.borrow(), dom) {
                                if seen.insert((level + 1, new_psum)) {
                                    queue.push_back(child.clone());
                                }
                            } else {
                                // we must not use this node under current bounds
                                sink.add_assumption(nlit(child.borrow().bool_var));
                            }
                        } else if !self.is_solution(new_psum) {
                            sink.add_clause(Clause::from([
                                nlit(node_var),
                                nlit(len_assign_var),
                                //plit(self.mdd_false),
                            ]));
                        };

                        let mut node = node.borrow_mut();
                        node.lo_hi = Some((current_l_bound, current_u_bound));
                    }
                }
                Monomial::Const(_) => {
                    todo!("Consts not supported: {}", self.linear)
                }
            }
        }
        if self.round == 1 {
            sink.add_clause(Clause::from([plit(root_var)]));
        }

        self.last_bounds = Some(dom.clone());
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct MddNode {
    level: usize,
    value: i64,
    bool_var: PVar,
    lo_hi: Option<(i64, i64)>,
}

impl MddNode {
    fn new(level: usize, value: i64) -> Self {
        Self {
            level,
            value,
            bool_var: pvar(),
            lo_hi: None,
        }
    }
}

impl Hash for MddNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.level.hash(state);
        self.value.hash(state);
    }
}
