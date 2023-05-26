//! Encodes linear constraints using the MDD encoding.

use std::{cell::RefCell, cmp::max, rc::Rc};

use indexmap::IndexMap;

use crate::{
    model::{
        words::{Symbol, WordEquation},
        Variable,
    },
    sat::{as_lit, neg, pvar, PVar},
};

use super::{substitution::SubstitutionEncoding, EncodingResult, PredicateEncoder, VariableBounds};

pub struct LinearEqEncoder {
    /// Maps variable to their coefficient in the equation
    coefficients: IndexMap<Variable, isize>,

    /// The right-hand side of the equation
    target: isize,

    /// The root of the MDD, is None prior to first call to `encode`
    mdd_root: Option<Rc<RefCell<MddNode>>>,

    /// The maximum length of each variable
    max_lengths: IndexMap<Variable, usize>,

    /// Assigns an arbitrary index to each variable
    var2index: IndexMap<Variable, usize>,
    /// Invers of `var2index`
    index2var: IndexMap<usize, Variable>,

    /// Maps nodes given as (variable, length) pairs to their corresponding SAT variables
    node_vars: IndexMap<(Variable, isize), PVar>,
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

        Self {
            coefficients,
            target,
            max_lengths: IndexMap::new(),
            mdd_root: None,
            var2index,
            index2var,
            node_vars: IndexMap::new(),
        }
    }

    fn build_mdd(&mut self, lenghts: &VariableBounds) {
        // Do BFS and extend the MDD with new nodes
        let mut queue = Vec::new();
        if self.mdd_root.is_none() {
            let root = MddNode::new(None, 0);
            self.mdd_root = Some(Rc::new(RefCell::new(root)));
        }

        queue.push(self.mdd_root.clone().unwrap());

        while let Some(v) = queue.pop() {
            let value = v.borrow().value;
            let var = v.borrow().variable.clone();
            let vindex = var.map(|v| self.var2index[&v]).unwrap_or(0);
            // Check if there is a successor row
            if let Some(vsucc) = self.index2var.get(&(vindex + 1)).cloned() {
                // Extend row with all possible values
                for l in 0..=lenghts.get(&vsucc) {
                    let new_value = value + self.coefficients[&vsucc] * l as isize;
                    let new_node = MddNode::new(Some(vsucc.clone()), new_value);
                    let rc = Rc::new(RefCell::new(new_node));
                    // Add as child
                    v.borrow_mut().add_child(rc.clone());
                    // Push to queue
                    queue.push(rc);
                }
            } else {
                // Is last row, check if target is reached
                if value == self.target {
                    v.borrow_mut().is_final = true;
                }
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

        let initial = self.mdd_root.clone().unwrap();
        let initial_var = pvar();
        result.add_clause(vec![as_lit(initial_var)]);

        let mut queue = Vec::new();
        queue.push((initial, initial_var));
        while let Some((parent_node, parent_node_var)) = queue.pop() {
            for child in parent_node.borrow().children.iter() {
                let child_var = child.borrow().variable.clone().unwrap();
                let child_node_var = self.get_or_create_node_var(
                    child.borrow().variable.as_ref().unwrap(),
                    child.borrow().value,
                );
                // If this an child is active, then the length must be accordingly
                // child.value = parent.value + child.coeff * child.length
                // <=> child.length = (child.value - parent.value) / child.coeff
                let coeff = self.coefficients[&child_var];
                assert!((child.borrow().value - parent_node.borrow().value) % coeff == 0);
                let len = (child.borrow().value - parent_node.borrow().value) / coeff;
                assert!(len >= 0);
                let len_var = length_encoding.get_len(&child_var, len as usize).unwrap();
                let clause = vec![neg(parent_node_var), neg(child_node_var), as_lit(len_var)];
                result.add_clause(clause);
                queue.push((child.clone(), child_node_var));
            }
        }

        result
    }
}

#[derive(Clone, Debug)]
struct MddNode {
    /// The variable that this node represents, is None if it is the root node
    variable: Option<Variable>,
    /// The partial sum of the coefficients of the variables in the path to this node
    value: isize,
    /// The children of this node
    children: Vec<Rc<RefCell<MddNode>>>,
    /// The node is final if it is the last node in the MDD and the value is equal to the target
    is_final: bool,

    can_reach_final: Option<bool>,
}

impl MddNode {
    fn new(variable: Option<Variable>, value: isize) -> Self {
        Self {
            variable,
            value,
            children: Vec::new(),
            is_final: false,
            can_reach_final: None,
        }
    }

    fn add_child(&mut self, child: Rc<RefCell<MddNode>>) {
        self.children.push(child);
    }

    fn minimize(&mut self) {
        //TODO
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
        self.encode_mdd(substitution)
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
