use std::{rc::Rc, time::Instant};

use indexmap::IndexMap;
use regulaer::{
    automaton::NFA,
    compiler::{Compiler, Thompson},
    re::Regex,
};

use super::{
    canonical::{Atom, AtomKind, Literal},
    Sort, Sorted, Variable,
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

    /// Registry of atoms, indexed by kind
    atom_registry: IndexMap<AtomKind, Rc<Atom>>,

    /// Registry of variables, indexed by name
    variables: IndexMap<String, Rc<Variable>>,

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
            NodeKind::Ite if children.len() == 3 => {
                let else_branch = children.pop().unwrap();
                let then_branch = children.pop().unwrap();
                let ifc = children.pop().unwrap();
                self.ite(ifc, then_branch, else_branch)
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
            NodeKind::Neg if children.len() == 1 => self.neg(children.pop().unwrap()),
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

            _ => panic!(
                "Invalid arity ({}) for kind {kind} ({:?})",
                children.len(),
                kind
            ),
        }
    }

    pub(crate) fn intern_node(&mut self, kind: NodeKind, children: Vec<Node>) -> Node {
        let children = if kind.is_commutative() {
            sort_commutative_args(children)
        } else {
            children
        };
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
        // for key in to_remove {
        //     // Remove the node from the pattern registry
        //     self.patterns.remove(&self.node_registry[&key]);
        //     // Remove the node from the node registry
        //     self.node_registry.remove(&key);
        // }
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

            let mut nfa = Thompson::default()
                .compile(regex, builder)
                .map(|nfa| nfa.remove_epsilons().expect("Failed to compile regex"))
                .expect("Failed to compile regex");

            nfa.trim();

            let nfa = Rc::new(nfa);
            self.nfas.insert(regex.clone(), nfa.clone());
            nfa
        };
        log::debug!("Compiled NFA ({:?})", t.elapsed());
        nfa
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
        if rs.is_empty() {
            return self.ttrue();
        } else if rs.len() == 1 {
            return rs[0].clone();
        } else {
            self.intern_node(NodeKind::And, rs)
        }
    }

    /// Boolean disjunction
    pub fn or(&mut self, rs: Vec<Node>) -> Node {
        self.intern_node(NodeKind::Or, rs)
    }

    /// Boolean negation
    pub fn not(&mut self, r: Node) -> Node {
        if let Some(b) = r.as_bool_const() {
            self.intern_node(NodeKind::Bool(!b), vec![])
        } else if *r.kind() == NodeKind::Not {
            // double negation
            r.children().first().unwrap().clone()
        } else {
            self.intern_node(NodeKind::Not, vec![r])
        }
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
        self.intern_node(NodeKind::Ite, vec![ifc, then_branch, else_branch])
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

    pub fn const_regex(&mut self, r: Regex) -> Node {
        self.intern_node(NodeKind::Regex(r), vec![])
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

        // Perform concatenation on constants
        let mut folded = Vec::new();
        let mut const_str = String::new();
        for node in flattened {
            if let Some(s) = node.as_str_const() {
                const_str.push_str(&s);
            } else {
                if !const_str.is_empty() {
                    folded.push(self.const_str(&const_str));
                    const_str.clear();
                }
                folded.push(node.clone());
            }
        }
        if !const_str.is_empty() {
            folded.push(self.const_str(&const_str));
        }

        if folded.is_empty() {
            self.const_str("")
        } else if folded.len() == 1 {
            folded.pop().unwrap()
        } else {
            self.intern_node(NodeKind::Concat, folded)
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
    pub fn const_int(&mut self, i: i64) -> Node {
        self.intern_node(NodeKind::Int(i), vec![])
    }

    /// Addition
    pub fn add(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        if rs.is_empty() {
            self.const_int(0)
        } else if rs.len() == 1 {
            rs[0].clone()
        } else {
            self.intern_node(NodeKind::Add, rs)
        }
    }

    /// Multiplication
    pub fn mul(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        if rs.is_empty() {
            self.const_int(1)
        } else if rs.len() == 1 {
            return rs[0].clone();
        } else {
            self.intern_node(NodeKind::Mul, rs)
        }
    }

    /// Subtraction
    pub fn sub(&mut self, rs: Vec<Node>) -> Node {
        debug_assert!(rs.iter().all(|n| n.sort().is_int()));
        if rs.is_empty() {
            self.const_int(0)
        } else if rs.len() == 1 {
            self.neg(rs[0].clone())
        } else {
            self.intern_node(NodeKind::Sub, rs)
        }
    }

    /// Negation
    pub fn neg(&mut self, r: Node) -> Node {
        debug_assert!(r.sort().is_int());
        if let Some(i) = r.as_int_const() {
            self.const_int(-i)
        } else if *r.kind() == NodeKind::Neg {
            // double negation
            r.children().first().unwrap().clone()
        } else {
            self.intern_node(NodeKind::Neg, vec![r])
        }
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

    /* Literals */

    pub fn literal(&mut self, lit: Literal) -> Node {
        self.intern_node(NodeKind::Literal(lit), vec![])
    }

    pub fn atom(&mut self, kind: AtomKind) -> Rc<Atom> {
        if let Some(atom) = self.atom_registry.get(&kind) {
            return atom.clone();
        } else {
            let id = self.next_id;
            self.next_id += 1;
            let atom = Rc::new(Atom::new(kind.clone(), id));
            self.atom_registry.insert(kind.clone(), atom.clone());
            atom
        }
    }
}

/// Some functions are commutative, so we can sort the arguments to make them easier to compare.
/// We sort to the arguments by the value of the node's id.
/// This way, we do not have "f(a, b)" and "f(b, a)" for commutative function f as separate nodes, but only one.
fn sort_commutative_args(nodes: Vec<Node>) -> Vec<Node> {
    let mut nodes = nodes;
    nodes.sort_by_key(|n| n.id);
    nodes
}
