use std::rc::Rc;

use indexmap::IndexMap;

use crate::{
    context::{Sorted, Variable},
    ir::{Pattern, Symbol},
};

use super::{Node, NodeKind, OwnedNode};

/// The type we use for hash-consing nodes
type ConsType = (NodeKind, Vec<Node>);

#[derive(Default)]
pub struct NodeManager {
    /// Counter for unique identifiers
    counter: usize,

    re_builder: regulaer::re::ReBuilder,

    /// Registry of nodes
    node_registry: IndexMap<ConsType, Node>,

    /// Registry of patterns, indexed by node
    patterns: IndexMap<Node, Rc<Pattern>>,
}

impl NodeManager {
    pub(crate) fn create_node(&mut self, kind: NodeKind, children: Vec<Node>) -> Node {
        let key = (kind.clone(), children.clone());
        let res = if let Some(rc_node) = self.node_registry.get(&key) {
            return rc_node.clone();
        } else {
            let node = OwnedNode::new(self.counter, kind, children);
            let rc_node = Rc::new(node.clone());
            self.node_registry.insert(key, rc_node.clone());
            self.counter += 1;
            rc_node
        };

        // every 100 nodes, garbage collect
        if (self.counter + 1) % 100 == 0 {
            self.gc();
        }
        res
    }

    /// Delete all nodes with reference count of 1
    fn gc(&mut self) {
        let mut to_remove = Vec::new();
        for (key, rc_node) in self.node_registry.iter() {
            if Rc::strong_count(rc_node) == 1 {
                to_remove.push(key.clone());
            }
        }
        for key in to_remove {
            // Remove the node from the pattern registry
            self.patterns.remove(&self.node_registry[&key]);
            // Remove the node from the node registry
            self.node_registry.remove(&key);
        }
    }

    /* Regex */

    pub fn re_builder(&mut self) -> &mut regulaer::re::ReBuilder {
        &mut self.re_builder
    }

    /* Node to Pattern conversions */

    /// Convert a node to a pattern.
    /// Returns None if the node is not a concatenation of variables and strings.
    pub fn patternize(&mut self, node: &Node) -> Option<Rc<Pattern>> {
        if let Some(pattern) = self.patterns.get(node) {
            return Some(pattern.clone());
        }
        let res = match node.kind() {
            NodeKind::String(s) => Pattern::constant(s),
            NodeKind::Variable(rc) => {
                debug_assert!(rc.sort().is_string());
                Pattern::variable(rc.as_ref())
            }
            NodeKind::Concat => {
                let mut pattern = Pattern::empty();
                for child in node.children() {
                    pattern.concat(self.patternize(child)?.as_ref().clone());
                }
                pattern
            }
            _ => return None,
        };
        let res = Rc::new(res);
        self.patterns.insert(node.clone(), res.clone());
        Some(res)
    }

    /// Convert a pattern to a node
    pub fn depatternize(&mut self, pattern: &Pattern) -> Node {
        let mut nodes = Vec::new();
        let mut word = String::new();
        for s in pattern.iter() {
            match s {
                Symbol::Constant(c) => {
                    word.push(*c);
                }
                Symbol::Variable(variable) => {
                    if !word.is_empty() {
                        nodes.push(self.create_node(NodeKind::String(word.clone()), vec![]));
                        word.clear();
                    }
                    nodes.push(self.var(Rc::new(variable.clone())));
                    word.clear();
                }
            }
        }
        if !word.is_empty() {
            nodes.push(self.create_node(NodeKind::String(word.clone()), vec![]));
            word.clear();
        }
        if nodes.is_empty() {
            // Empty pattern = empty string
            self.const_str("")
        } else if nodes.len() == 1 {
            nodes[0].clone()
        } else {
            self.concat(nodes)
        }
    }

    /* Constructions */

    /* Boolean Functions */

    /// A variable
    pub fn var(&mut self, var: Rc<Variable>) -> Node {
        self.create_node(NodeKind::Variable(var), vec![])
    }

    /// The Boolean constant `false`
    pub fn ffalse(&mut self) -> Node {
        self.create_node(NodeKind::Bool(false), vec![])
    }

    /// The Boolean constant `true`
    pub fn ttrue(&mut self) -> Node {
        self.create_node(NodeKind::Bool(true), vec![])
    }

    /// Boolean conjunction
    pub fn and(&mut self, rs: Vec<Node>) -> Node {
        self.create_node(NodeKind::And, rs)
    }

    /// Boolean disjunction
    pub fn or(&mut self, rs: Vec<Node>) -> Node {
        self.create_node(NodeKind::Or, rs)
    }

    /// Boolean negation
    pub fn not(&mut self, r: Node) -> Node {
        self.create_node(NodeKind::Not, vec![r])
    }

    /// Boolean implication
    pub fn imp(&mut self, l: Node, r: Node) -> Node {
        self.create_node(NodeKind::Imp, vec![l, r])
    }

    /// Boolean equivalence
    pub fn equiv(&mut self, l: Node, r: Node) -> Node {
        self.create_node(NodeKind::Equiv, vec![l, r])
    }

    /* Equality */

    /// Equality
    pub fn eq(&mut self, l: Node, r: Node) -> Node {
        self.create_node(NodeKind::Eq, vec![l, r])
    }

    /* String Functions */

    /// A string constant
    pub fn const_string(&mut self, s: String) -> Node {
        self.create_node(NodeKind::String(s), vec![])
    }

    /// A string constant, given a string slice.
    /// This is a convenience function that converts the slice to a `String`.
    pub fn const_str(&mut self, s: &str) -> Node {
        self.const_string(s.to_string())
    }

    /// String concatenation
    pub fn concat(&mut self, rs: Vec<Node>) -> Node {
        self.create_node(NodeKind::Concat, rs)
    }
}
