use std::{rc::Rc, time::Instant};

use indexmap::IndexMap;
use regulaer::{
    automaton::NFA,
    compiler::{Compiler, Thompson},
    re::Regex,
};

use crate::{
    context::{Sort, Sorted, Variable},
    ir::{Pattern, Symbol},
};

use super::{error::NodeError, Node, NodeKind, OwnedNode};

/// The type we use for hash-consing nodes
type NodeKey = (NodeKind, Vec<Node>);

#[derive(Default)]
pub struct NodeManager {
    /// Counter for unique identifiers
    next_id: usize,

    /// Regular expression builder
    re_builder: regulaer::re::ReBuilder,

    /// Registry of nodes
    node_registry: IndexMap<NodeKey, Node>,

    /// Registry of variables, indexed by name
    variables: IndexMap<String, Rc<Variable>>,

    /// Registry of patterns, indexed by node
    patterns: IndexMap<Node, Rc<Pattern>>,

    nfas: IndexMap<Regex, Rc<NFA>>,
}

impl NodeManager {
    pub fn create_node(&mut self, kind: NodeKind, mut children: Vec<Node>) -> Node {
        match kind {
            NodeKind::Bool(_)
            | NodeKind::String(_)
            | NodeKind::Int(_)
            | NodeKind::Regex(_)
            | NodeKind::Variable(_)
                if children.is_empty() =>
            {
                self.intern_node(kind, children)
            }
            NodeKind::Or => self.or(children),
            NodeKind::And => self.and(children),
            NodeKind::Imp if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.imp(l, r)
            }
            NodeKind::Equiv if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.equiv(l, r)
            }
            NodeKind::Not if children.len() == 1 => self.not(children.pop().unwrap()),
            NodeKind::Eq if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.eq(l, r)
            }
            NodeKind::Concat => self.concat(children),
            NodeKind::Length if children.len() == 1 => {
                let c = children.pop().unwrap();
                self.str_len(c)
            }
            NodeKind::InRe if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.in_re(l, r)
            }
            NodeKind::PrefixOf if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.prefix_of(l, r)
            }
            NodeKind::SuffixOf if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.suffix_of(l, r)
            }
            NodeKind::Contains if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.contains(l, r)
            }
            NodeKind::Add => self.add(children),
            NodeKind::Sub => self.sub(children),
            NodeKind::Mul => self.mul(children),
            NodeKind::Lt if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.lt(l, r)
            }
            NodeKind::Le if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.le(l, r)
            }
            NodeKind::Gt if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.gt(l, r)
            }
            NodeKind::Ge if children.len() == 2 => {
                let r = children.pop().unwrap();
                let l = children.pop().unwrap();
                self.ge(l, r)
            }
            _ => panic!("Invalid arity ({}) for kind {kind}", children.len()),
        }
    }

    pub(crate) fn intern_node(&mut self, kind: NodeKind, children: Vec<Node>) -> Node {
        let key = (kind.clone(), children.clone());
        let res = if let Some(rc_node) = self.node_registry.get(&key) {
            return rc_node.clone();
        } else {
            let node = OwnedNode::new(self.next_id, kind, children);
            let rc_node = Rc::new(node.clone());
            self.node_registry.insert(key, rc_node.clone());
            self.next_id += 1;
            rc_node
        };

        // every 100 nodes, garbage collect
        if (self.next_id + 1) % 100 == 0 {
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
        log::trace!("GC: Removing {} nodes", to_remove.len());
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

    /// Returns the NFA for the given regular expression.
    /// Computes the NFA if it has not been computed yet.
    pub fn get_nfa(&mut self, regex: &Regex) -> Rc<NFA> {
        let t = Instant::now();
        let nfa = if let Some(nfa) = self.nfas.get(regex) {
            nfa.clone()
        } else {
            let builder = self.re_builder();

            let nfa = Thompson::default()
                .compile(regex, builder)
                .map(|nfa| nfa.remove_epsilons().expect("Failed to compile regex"))
                .expect("Failed to compile regex");

            let nfa = Rc::new(nfa);
            self.nfas.insert(regex.clone(), nfa.clone());
            nfa
        };
        log::debug!("Compiled NFA ({:?})", t.elapsed());
        nfa
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
                Pattern::variable(rc)
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
                        nodes.push(self.intern_node(NodeKind::String(word.clone()), vec![]));
                        word.clear();
                    }
                    let v = self.get_var(variable.name()).unwrap();
                    nodes.push(self.var(v));
                    word.clear();
                }
            }
        }
        if !word.is_empty() {
            nodes.push(self.intern_node(NodeKind::String(word.clone()), vec![]));
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

    /* Variables */

    /// Creates a new variable with a given name and sort.
    /// If that variable already exists, returns the existing variable.
    /// If a variable with the same name but different sort exists, panics.
    pub fn new_var(&mut self, name: String, sort: Sort) -> Result<Rc<Variable>, NodeError> {
        if let Some(var) = self.variables.get(&name) {
            if var.sort() != sort {
                return Err(NodeError::AlreadyDeclared(name, sort, var.sort()));
            }
            Ok(var.clone())
        } else {
            let var = Rc::new(Variable::new(self.next_id, name.clone(), sort));
            self.next_id += 1;
            self.variables.insert(name.clone(), var.clone());
            Ok(var)
        }
    }

    pub fn get_var(&self, name: &str) -> Option<Rc<Variable>> {
        self.variables.get(name).cloned()
    }

    /// Creates a new temporary variable with a given sort.
    pub fn temp_var(&mut self, sort: Sort) -> Rc<Variable> {
        let name = format!("__temp_{}", self.next_id);
        self.next_id += 1;
        self.new_var(name, sort).unwrap() // safe to unwrap
    }

    pub fn vars(&self) -> impl Iterator<Item = &Rc<Variable>> {
        self.variables.values()
    }

    /* Constructions */

    /* Boolean Functions */

    /// A variable
    pub fn var(&mut self, var: Rc<Variable>) -> Node {
        self.intern_node(NodeKind::Variable(var), vec![])
    }

    /// The Boolean constant `false`
    pub fn ffalse(&mut self) -> Node {
        self.intern_node(NodeKind::Bool(false), vec![])
    }

    /// The Boolean constant `true`
    pub fn ttrue(&mut self) -> Node {
        self.intern_node(NodeKind::Bool(true), vec![])
    }

    /// Boolean conjunction
    pub fn and(&mut self, rs: Vec<Node>) -> Node {
        self.intern_node(NodeKind::And, rs)
    }

    /// Boolean disjunction
    pub fn or(&mut self, rs: Vec<Node>) -> Node {
        self.intern_node(NodeKind::Or, rs)
    }

    /// Boolean negation
    pub fn not(&mut self, r: Node) -> Node {
        self.intern_node(NodeKind::Not, vec![r])
    }

    /// Boolean implication
    pub fn imp(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::Imp, vec![l, r])
    }

    /// Boolean equivalence
    pub fn equiv(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::Equiv, vec![l, r])
    }

    pub fn ite(&mut self, ifc: Node, then_branch: Node, else_branch: Node) -> Node {
        self.create_node(NodeKind::Ite, vec![ifc, then_branch, else_branch])
    }

    /* Equality */

    /// Equality
    pub fn eq(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::Eq, vec![l, r])
    }

    /* String Functions */

    /// A string constant
    pub fn const_string(&mut self, s: String) -> Node {
        self.intern_node(NodeKind::String(s), vec![])
    }

    /// A string constant, given a string slice.
    /// This is a convenience function that converts the slice to a `String`.
    pub fn const_str(&mut self, s: &str) -> Node {
        self.const_string(s.to_string())
    }

    /// String concatenation
    pub fn concat(&mut self, rs: Vec<Node>) -> Node {
        // Flatten the concatenation and remove empty strings
        let flattened = rs
            .into_iter()
            .flat_map(|node| {
                if let NodeKind::Concat = node.kind() {
                    node.children().to_vec()
                } else {
                    vec![node]
                }
            })
            .filter(|n| !matches!(n.kind(), NodeKind::String(s) if s.is_empty()));

        // if there is only one node, return it
        let mut flattened = flattened.collect::<Vec<_>>();
        if flattened.is_empty() {
            self.const_str("")
        } else if flattened.len() == 1 {
            flattened.pop().unwrap()
        } else {
            self.intern_node(NodeKind::Concat, flattened)
        }
    }

    pub fn str_len(&mut self, s: Node) -> Node {
        self.intern_node(NodeKind::Length, vec![s])
    }

    pub fn prefix_of(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::PrefixOf, vec![l, r])
    }

    pub fn suffix_of(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::SuffixOf, vec![l, r])
    }

    pub fn contains(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::Contains, vec![l, r])
    }

    /// Regular Membership
    pub fn in_re(&mut self, l: Node, r: Node) -> Node {
        self.intern_node(NodeKind::InRe, vec![l, r])
    }

    /* Int Functions */

    /// An integer constant
    pub fn int(&mut self, i: i64) -> Node {
        self.intern_node(NodeKind::Int(i), vec![])
    }

    /// Addition
    pub fn add(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        self.intern_node(NodeKind::Add, rs)
    }

    /// Multiplication
    pub fn mul(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        self.intern_node(NodeKind::Mul, rs)
    }

    /// Subtraction
    pub fn sub(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        self.intern_node(NodeKind::Sub, rs)
    }

    /// Negation
    pub fn neg(&mut self, r: Node) -> Node {
        debug_assert!(r.sort().is_int());
        self.intern_node(NodeKind::Neg, vec![r])
    }

    /// Less than
    pub fn lt(&mut self, l: Node, r: Node) -> Node {
        debug_assert!(l.sort().is_int());
        debug_assert!(r.sort().is_int());
        self.intern_node(NodeKind::Lt, vec![l, r])
    }

    /// Less than or equal
    pub fn le(&mut self, l: Node, r: Node) -> Node {
        debug_assert!(l.sort().is_int());
        debug_assert!(r.sort().is_int());
        self.intern_node(NodeKind::Le, vec![l, r])
    }

    /// Greater than
    pub fn gt(&mut self, l: Node, r: Node) -> Node {
        debug_assert!(l.sort().is_int());
        debug_assert!(r.sort().is_int());
        self.intern_node(NodeKind::Gt, vec![l, r])
    }

    /// Greater than or equal
    pub fn ge(&mut self, l: Node, r: Node) -> Node {
        debug_assert!(l.sort().is_int());
        debug_assert!(r.sort().is_int());
        self.intern_node(NodeKind::Ge, vec![l, r])
    }
}
