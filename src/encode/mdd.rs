//! Encodes linear constraints using the MDD encoding.

use std::{borrow::BorrowMut, cell::RefCell, rc::Rc};

use indexmap::IndexMap;

use crate::{
    model::{
        words::{Symbol, WordEquation},
        Variable,
    },
    sat::{as_lit, neg, pvar, PVar},
};

use super::IntegerDomainBounds;
use super::{domain::SubstitutionEncoding, EncodingResult, PredicateEncoder};

pub struct LinearEqEncoder {
    /// Maps variable to their coefficient in the equation
    coefficients: IndexMap<Variable, isize>,

    /// The right-hand side of the equation
    target: isize,

    /// The root of the MDD, is None prior to first call to `encode`
    mdd_root: Option<Rc<RefCell<MddNode>>>,
    mdd_final_t: Rc<RefCell<MddNode>>,
    mdd_final_f: Rc<RefCell<MddNode>>,

    /// The maximum length of each variable

    /// Assigns an arbitrary index to each variable
    var2index: IndexMap<Variable, usize>,
    /// Invers of `var2index`
    index2var: IndexMap<usize, Variable>,

    row_values: IndexMap<(Variable, isize), Rc<RefCell<MddNode>>>,

    init_node_var: Option<PVar>,
    t_node_var: PVar,
    f_node_var: PVar,

    /// Maps nodes given as (variable, length) pairs to their corresponding SAT variables
    node_vars: IndexMap<(Variable, isize), PVar>,

    last_lengths: Option<VariableBounds>,
}

impl LinearEqEncoder {
    pub fn from_word_equation(equation: &WordEquation) -> Self {
        let mut coefficients = IndexMap::new();
        let mut target = 0;
        let mut var2index = IndexMap::new();
        let mut index2var = IndexMap::new();
        let mut index = 0;
        for x in equation.variables() {
            let xs = &Symbol::Variable(x.clone());
            let coeff = equation.lhs().count(xs) as isize - equation.rhs().count(xs) as isize;
            var2index.insert(x.clone(), index);
            index2var.insert(index, x.clone());
            index += 1;
            coefficients.insert(x, coeff as isize);
        }
        for c in equation.alphabet() {
            let c = &Symbol::Constant(c);
            let coeff = equation.rhs().count(c) as isize - equation.lhs().count(c) as isize;
            target += coeff as isize;
        }
        let final_t = MddNode::new(NodeType::Terminal(true), -1);
        let final_f = MddNode::new(NodeType::Terminal(false), -1);

        Self {
            coefficients,
            target,
            mdd_root: None,
            var2index,
            index2var,
            node_vars: IndexMap::new(),
            row_values: IndexMap::new(),
            last_lengths: None,
            mdd_final_t: Rc::new(RefCell::new(final_t)),
            mdd_final_f: Rc::new(RefCell::new(final_f)),
            init_node_var: None,
            t_node_var: pvar(),
            f_node_var: pvar(),
        }
    }

    fn build_mdd(&mut self, lenghts: &VariableBounds) {
        // Do BFS and extend the MDD with new nodes
        let rootvar = self.coefficients.first().unwrap().0.clone();
        let mut queue = Vec::new();
        if self.mdd_root.is_none() {
            let root = MddNode::new(NodeType::NonTerminal(rootvar), 0);
            self.mdd_root = Some(Rc::new(RefCell::new(root)));
        }

        queue.push(self.mdd_root.clone().unwrap());

        while let Some(v) = queue.pop() {
            let value = v.borrow().value;
            let ntype = v.borrow().ntype.clone();
            match ntype {
                NodeType::NonTerminal(var) => {
                    let vindex = self.var2index[&var];
                    let lastlen = self
                        .last_lengths
                        .as_ref()
                        .map(|l| l.get(&var) + 1)
                        .unwrap_or(0);
                    if let Some(vsucc) = self.index2var.get(&(vindex + 1)).cloned() {
                        for l in lastlen..=lenghts.get(&var) {
                            let new_value = value + self.coefficients[&var] * l as isize;
                            let child =
                                self.row_values
                                    .entry((var.clone(), new_value))
                                    .or_insert(Rc::new(RefCell::new(MddNode::new(
                                        NodeType::NonTerminal(vsucc.clone()),
                                        new_value,
                                    ))));
                            // Add as child
                            v.borrow_mut().add_child(l, child.clone());
                            // Push to queue
                            queue.push(child.clone());
                        }
                    } else {
                        // Is last row, check if target is reached
                        for l in lastlen..=lenghts.get(&var) {
                            let new_value = value + self.coefficients[&var] * l as isize;
                            let dest = if new_value == self.target {
                                self.mdd_final_t.clone()
                            } else {
                                self.mdd_final_f.clone()
                            };
                            v.borrow_mut().add_child(l, dest);
                        }
                    }
                }
                NodeType::Terminal(_) => todo!(),
            }
        }
    }

    fn get_or_create_node_var(&mut self, var: &Variable, value: isize) -> PVar {
        self.node_vars
            .entry((var.clone(), value))
            .or_insert_with(|| pvar())
            .clone()
    }

    fn encode_mdd(&mut self, length_encoding: &SubstitutionEncoding) -> EncodingResult {
        let mut result = EncodingResult::empty();

        if self.init_node_var.is_none() {
            self.init_node_var = Some(pvar());
            result.add_clause(vec![as_lit(self.init_node_var.unwrap())]);
        }

        let mut queue = Vec::new();
        queue.push(self.mdd_root.as_ref().unwrap().clone());
        while let Some(parent) = queue.pop() {
            match &parent.borrow().ntype {
                NodeType::NonTerminal(parent_var) => {
                    let parent_val = parent.borrow().value;
                    let parent_node_var = self.get_or_create_node_var(&parent_var, parent_val);
                    for (l, child) in parent.borrow().children.iter() {
                        let len_var = length_encoding.get_len(parent_var, *l).unwrap();
                        match &child.borrow().ntype {
                            NodeType::NonTerminal(child_var) => {
                                let child_node_var =
                                    self.get_or_create_node_var(&child_var, child.borrow().value);

                                result.add_clause(vec![
                                    as_lit(child_node_var),
                                    neg(len_var),
                                    neg(parent_node_var),
                                ]);
                                result.add_clause(vec![
                                    neg(child_node_var),
                                    neg(len_var),
                                    as_lit(parent_node_var),
                                ]);
                                queue.push(child.clone());
                            }
                            NodeType::Terminal(true) => {
                                result.add_clause(vec![
                                    as_lit(self.t_node_var),
                                    neg(len_var),
                                    neg(parent_node_var),
                                ]);
                                result.add_clause(vec![
                                    neg(self.t_node_var),
                                    neg(len_var),
                                    as_lit(parent_node_var),
                                ]);
                            }
                            NodeType::Terminal(false) => {
                                result.add_clause(vec![
                                    as_lit(self.f_node_var),
                                    neg(len_var),
                                    neg(parent_node_var),
                                ]);
                                result.add_clause(vec![
                                    neg(self.f_node_var),
                                    neg(len_var),
                                    as_lit(parent_node_var),
                                ]);
                            }
                        }
                    }
                }
                NodeType::Terminal(_) => {}
            }
        }
        result.add_clause(vec![neg(self.f_node_var)]);

        result
    }
}

#[derive(Clone, Debug)]
enum NodeType {
    NonTerminal(Variable),
    Terminal(bool),
}

#[derive(Clone, Debug)]
struct MddNode {
    /// The variable that this node represents, is None if it is the root node
    ntype: NodeType,
    /// The partial sum of the coefficients of the variables in the path to this node
    value: isize,
    /// The children of this node
    children: Vec<(usize, Rc<RefCell<MddNode>>)>,
}

impl MddNode {
    fn new(ntype: NodeType, value: isize) -> Self {
        Self {
            ntype,
            value,
            children: Vec::new(),
        }
    }

    fn add_child(&mut self, v: usize, child: Rc<RefCell<MddNode>>) {
        self.children.push((v, child));
    }
}

impl PredicateEncoder for LinearEqEncoder {
    fn encode(
        &mut self,
        bounds: &VariableBounds,
        substitution: &SubstitutionEncoding,
    ) -> EncodingResult {
        // Create the MDD
        self.build_mdd(&bounds);

        assert!(self.mdd_root.is_some());

        // Encode the MDD
        let res: EncodingResult = self.encode_mdd(substitution);
        self.last_lengths = Some(bounds.clone());
        res
    }

    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {}
}

#[cfg(test)]
mod Tests {

    use super::*;

    #[test]
    fn test_mdd() {}
}
