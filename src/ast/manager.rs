use std::{collections::VecDeque, rc::Rc};

use indexmap::{IndexMap, IndexSet};

use smt_str::{re::Regex, SmtString};

use crate::context::{Sort, Sorted, Variable};

use super::{Node, NodeKind, OwnedNode};

/// The type we use for hash-consing nodes
type NodeKey = (NodeKind, Vec<Node>);

pub struct AstBuilder {
    /// Counter for unique identifiers
    next_id: usize,

    /// Registry of nodes
    node_registry: IndexMap<NodeKey, Node>,

    /// If false, will perform no optimizations
    simplify: bool,
}

impl Default for AstBuilder {
    fn default() -> Self {
        Self {
            next_id: 0,
            node_registry: IndexMap::new(),
            simplify: true,
        }
    }
}

impl AstBuilder {
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
            NodeKind::SubStr if children.len() == 3 => {
                let end = children.pop().unwrap();
                let start = children.pop().unwrap();
                let s = children.pop().unwrap();
                self.substr(s, start, end)
            }
            NodeKind::At if children.len() == 2 => {
                let i = children.pop().unwrap();
                let s = children.pop().unwrap();
                self.at(s, i)
            }
            NodeKind::Replace if children.len() == 3 => {
                let to = children.pop().unwrap();
                let from = children.pop().unwrap();
                let s = children.pop().unwrap();
                self.str_replace(s, from, to)
            }
            NodeKind::ToInt if children.len() == 1 => {
                let s = children.pop().unwrap();
                self.str_to_int(s)
            }
            NodeKind::FromInt if children.len() == 1 => {
                let i = children.pop().unwrap();
                self.str_from_int(i)
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
                "Unknown function or invalid arity ({}) for kind {kind} ({:?})",
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
            rc_node.clone()
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

    /// Set the optimization flag
    #[cfg(test)]
    pub(crate) fn set_simplify(&mut self, optimize: bool) {
        self.simplify = optimize;
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
            self.node_registry.remove(&key);
        }
    }

    /* Constructions */

    /* Boolean Functions */

    /// A variable
    pub fn variable(&mut self, var: Rc<Variable>) -> Node {
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

    /// Boolean conjunction.
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Removes all duplicates
    /// - Remove all `true` node
    /// - Return `false` upon `false` node
    /// - Return `false` if conjunction contains node and its negation
    /// - Flattens nested conjunctions
    /// - Returns `true` if the (simplified) arguments are empty
    pub fn and(&mut self, rs: Vec<Node>) -> Node {
        if self.simplify {
            let mut simped = IndexSet::with_capacity(rs.len());
            for r in rs {
                if let NodeKind::Bool(false) = r.kind() {
                    return self.ffalse();
                } else if let NodeKind::Bool(true) = r.kind() {
                    continue;
                } else if let NodeKind::And = r.kind() {
                    simped.extend(r.children().to_vec())
                } else {
                    // check if we have seen the negation
                    let negated = self.not(r.clone());
                    if simped.contains(&negated) {
                        return self.ffalse();
                    } else {
                        simped.insert(r);
                    }
                }
            }
            match simped.len() {
                0 => self.ttrue(),
                1 => simped[0].clone(),
                _ => self.intern_node(NodeKind::And, simped.into_iter().collect()),
            }
        } else {
            self.intern_node(NodeKind::And, rs)
        }
    }

    /// Boolean conjunction.
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Removes all duplicates
    /// - Remove all `false` node
    /// - Return `true` upon `true` node
    /// - Return `true` if conjunction contains node and its negation
    /// - Flattens nested disjunctions
    /// - Returns `false` if the (simplified) arguments are empty
    pub fn or(&mut self, rs: Vec<Node>) -> Node {
        if self.simplify {
            let mut simped = IndexSet::with_capacity(rs.len());
            for r in rs {
                if let NodeKind::Bool(true) = r.kind() {
                    return self.ttrue();
                } else if let NodeKind::Bool(false) = r.kind() {
                    continue;
                } else if let NodeKind::Or = r.kind() {
                    simped.extend(r.children().to_vec())
                } else {
                    // check if we have seen the negation
                    let negated = self.not(r.clone());
                    if simped.contains(&negated) {
                        return self.ttrue();
                    } else {
                        simped.insert(r);
                    }
                }
            }
            match simped.len() {
                0 => self.ffalse(),
                1 => simped[0].clone(),
                _ => self.intern_node(NodeKind::Or, simped.into_iter().collect()),
            }
        } else {
            self.intern_node(NodeKind::Or, rs)
        }
    }

    /// Boolean negation
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Returns `false` if node is `true`
    /// - Returns `true` if node is `false`
    /// - Eliminates double-negations
    /// - Flips the operator for lienar constraints instead of nesting in a `not` node
    /// - Replaces `not (=> a b)` with `(=> b a)`
    pub fn not(&mut self, r: Node) -> Node {
        if self.simplify {
            match r.kind() {
                NodeKind::Bool(false) => self.ttrue(),
                NodeKind::Bool(true) => self.ffalse(),
                NodeKind::Not => r.children().first().unwrap().clone(),
                NodeKind::Lt => {
                    let mut children = r.children().to_vec();
                    let r = children.pop().unwrap();
                    let l = children.pop().unwrap();
                    self.ge(l, r)
                }
                NodeKind::Le => {
                    let mut children = r.children().to_vec();
                    let r = children.pop().unwrap();
                    let l = children.pop().unwrap();
                    self.gt(l, r)
                }
                NodeKind::Gt => {
                    let mut children = r.children().to_vec();
                    let r = children.pop().unwrap();
                    let l = children.pop().unwrap();
                    self.le(l, r)
                }
                NodeKind::Ge => {
                    let mut children = r.children().to_vec();
                    let r = children.pop().unwrap();
                    let l = children.pop().unwrap();
                    self.lt(l, r)
                }
                NodeKind::Imp => {
                    // -(L -> R) <==> -(-L \/ R) <==> L /\ -R
                    let mut children = r.children().to_vec();
                    let r = children.pop().unwrap();
                    let l = children.pop().unwrap();
                    let not_r = self.not(r);
                    self.and(vec![l, not_r])
                }
                _ => self.intern_node(NodeKind::Not, vec![r]),
            }
        } else {
            self.intern_node(NodeKind::Not, vec![r])
        }
    }

    /// Boolean implication
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Returns `true` if `l` is `false`
    /// - Returns `r` if `l` is `true`
    /// - Returns `not(l)` if `r` is `false`
    /// - Returns `true` if `r` is `true`
    pub fn imp(&mut self, l: Node, r: Node) -> Node {
        if self.simplify {
            if let Some(b) = l.as_bool_const() {
                if b {
                    return r;
                } else {
                    return self.ttrue();
                }
            }
            if let Some(b) = r.as_bool_const() {
                if b {
                    return self.ttrue();
                } else {
                    return self.not(l);
                }
            }
        }
        self.intern_node(NodeKind::Imp, vec![l, r])
    }

    /// Boolean equivalence
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Returns `true` if `l` and `r` are syntactially equivalent
    /// - Returns `false` if `l` and `r` are constants and not equivalent equivalent
    pub fn equiv(&mut self, l: Node, r: Node) -> Node {
        debug_assert!(l.sort().is_bool());
        debug_assert!(r.sort().is_bool());

        if self.simplify {
            if l == r {
                return self.ttrue();
            } else if let (Some(l), Some(r)) = (l.as_bool_const(), r.as_bool_const()) {
                if l == r {
                    return self.ttrue();
                } else {
                    return self.ffalse();
                }
            }
        }
        self.intern_node(NodeKind::Equiv, vec![l, r])
    }

    /// IF-THEN-ELSE Expression
    ///
    /// Creates an `ite(i, t, e)` expression that evaluates to `t` if `i` is `true` and to `e` otherwise.
    ///
    /// ## Simplifications
    /// If `simplify` is enabled and `i` is a boolean constant, returns `t` or `e` accordingly
    pub fn ite(&mut self, ifc: Node, then_branch: Node, else_branch: Node) -> Node {
        if self.simplify {
            if let Some(b) = ifc.as_bool_const() {
                if b {
                    return then_branch;
                } else {
                    return else_branch;
                }
            }
        }
        self.intern_node(NodeKind::Ite, vec![ifc, then_branch, else_branch])
    }

    /* Equality */

    /// Equality
    ///
    /// ## Simplifications
    /// If `simplify` is enabled, performs the following simplifications:
    /// - Returns `true` if `l` and `r` are equal
    /// - Returns `false` if `l` and `r` are constants and not equal
    pub fn eq(&mut self, l: Node, r: Node) -> Node {
        if self.simplify {
            if l == r {
                return self.ttrue();
            } else {
                match (l.sort(), r.sort()) {
                    (Sort::String, Sort::String) => {
                        if let (Some(lc), Some(rc)) = (l.as_str_const(), r.as_str_const()) {
                            return if lc == rc {
                                self.ttrue()
                            } else {
                                self.ffalse()
                            };
                        }
                    }
                    (Sort::Int, Sort::Int) => {
                        if let (Some(lc), Some(rc)) = (l.as_int_const(), r.as_int_const()) {
                            return if lc == rc {
                                self.ttrue()
                            } else {
                                self.ffalse()
                            };
                        }
                    }
                    _ => todo!(),
                }
            }
        }

        self.intern_node(NodeKind::Eq, vec![l, r])
    }

    /* String Functions */

    /// A string constant
    pub fn const_string(&mut self, s: SmtString) -> Node {
        self.intern_node(NodeKind::String(s), vec![])
    }

    /// A string constant, given a string slice.
    /// This is a convenience function that converts the &str slice to a `SmtString`.
    /// The constant string is parse into a `SmtString` and then interned.
    /// This panics if `s` is not valid in SMT-LIB.
    pub fn const_str(&mut self, s: &str) -> Node {
        let s = SmtString::parse(s);
        self.const_string(s)
    }

    /// Reutns the empty string
    pub fn empty_string(&mut self) -> Node {
        self.const_string(SmtString::empty())
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
        let mut const_str = SmtString::empty();
        for node in flattened {
            if let Some(s) = node.as_str_const() {
                const_str.append(&s);
            } else {
                if !const_str.is_empty() {
                    folded.push(self.const_string(const_str.clone()));
                    const_str.clear();
                }
                folded.push(node.clone());
            }
        }
        if !const_str.is_empty() {
            folded.push(self.const_string(const_str));
        }

        if folded.is_empty() {
            self.const_str("")
        } else if folded.len() == 1 {
            folded.pop().unwrap()
        } else {
            self.intern_node(NodeKind::Concat, folded)
        }
    }

    /// String length
    ///
    /// ## Simplifications
    /// If `simplify` is enabled:
    /// - Returns `str.len(t1) + ... + str.len(tn)` if the argument is `(str.++ t1 ... tn)`
    /// - Replaces `str.len(w)` with the length of `w` if it is a constant
    pub fn str_len(&mut self, s: Node) -> Node {
        if self.simplify {
            if let NodeKind::Concat = *s.kind() {
                let mut sumands = Vec::with_capacity(s.children().len());
                for c in s.children() {
                    sumands.push(self.str_len(c.clone()));
                }
                return self.add(sumands);
            } else if let Some(w) = s.as_str_const() {
                return self.const_int(w.len() as i64);
            }
        }
        self.intern_node(NodeKind::Length, vec![s])
    }

    /// str.prefixof
    ///
    /// ## Simplifications
    /// If `simplify` is enabled an both arguments are constants, folds the term.
    pub fn prefix_of(&mut self, l: Node, r: Node) -> Node {
        if self.simplify {
            if let (Some(l), Some(r)) = (l.as_str_const(), r.as_str_const()) {
                if r.starts_with(&l) {
                    return self.ttrue();
                } else {
                    return self.ffalse();
                }
            }
        }
        self.intern_node(NodeKind::PrefixOf, vec![l, r])
    }

    /// str.suffixof
    ///
    /// ## Simplifications
    /// If `simplify` is enabled an both arguments are constants, folds the term.
    pub fn suffix_of(&mut self, l: Node, r: Node) -> Node {
        if self.simplify {
            if let (Some(l), Some(r)) = (l.as_str_const(), r.as_str_const()) {
                if r.ends_with(&l) {
                    return self.ttrue();
                } else {
                    return self.ffalse();
                }
            }
        }
        self.intern_node(NodeKind::SuffixOf, vec![l, r])
    }

    /// str.contains
    ///
    /// ## Simplifications
    /// If `simplify` is enabled an both arguments are constants, folds the term.
    pub fn contains(&mut self, l: Node, r: Node) -> Node {
        if self.simplify {
            if let (Some(l), Some(r)) = (l.as_str_const(), r.as_str_const()) {
                if l.contains(&r) {
                    return self.ttrue();
                } else {
                    return self.ffalse();
                }
            }
        }
        self.intern_node(NodeKind::Contains, vec![l, r])
    }

    /// str.substr
    ///
    /// ## Simplifications
    /// If `simplify` is enabled and the arguments are constants, folds the term.
    pub fn substr(&mut self, s: Node, start: Node, len: Node) -> Node {
        if self.simplify {
            if let (Some(start), Some(len)) = (start.as_int_const(), len.as_int_const()) {
                if start < 0 || len < 0 {
                    return self.empty_string();
                }
                if let Some(s) = s.as_str_const() {
                    return self.const_string(s.drop(start as usize).take(len as usize));
                }
            }
        }

        self.intern_node(NodeKind::SubStr, vec![s, start, len])
    }

    /// str.substr
    ///
    /// ## Simplifications
    /// If `simplify` is enabled an the arguments are constants, folds the term.
    pub fn at(&mut self, s: Node, i: Node) -> Node {
        if let Some(i) = i.as_int_const() {
            if i < 0 {
                return self.empty_string();
            } else if let Some(s) = s.as_str_const() {
                return self.const_string(s.drop(i as usize).take(1));
            }
        }
        self.intern_node(NodeKind::At, vec![s, i])
    }

    pub fn str_replace(&mut self, s: Node, from: Node, to: Node) -> Node {
        self.intern_node(NodeKind::Replace, vec![s, from, to])
    }

    pub fn str_replace_all(&mut self, s: Node, from: Node, to: Node) -> Node {
        self.intern_node(NodeKind::ReplaceAll, vec![s, from, to])
    }

    pub fn str_to_int(&mut self, s: Node) -> Node {
        self.intern_node(NodeKind::ToInt, vec![s])
    }

    pub fn str_from_int(&mut self, i: Node) -> Node {
        self.intern_node(NodeKind::FromInt, vec![i])
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
        let mut res = Vec::with_capacity(rs.len());
        let mut q = VecDeque::from_iter(rs);
        let mut c = 0;

        while let Some(r) = q.pop_front() {
            if let Some(i) = r.as_int_const() {
                c += i;
            } else if let NodeKind::Add = *r.kind() {
                q.extend(r.children().iter().cloned());
            } else {
                res.push(r);
            }
        }

        if c != 0 {
            res.push(self.const_int(c));
        }

        if res.is_empty() {
            self.const_int(0)
        } else if res.len() == 1 {
            res[0].clone()
        } else {
            self.intern_node(NodeKind::Add, res)
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

        if self.simplify {
            let mut as_sum = Vec::with_capacity(rs.len());
            if let Some(f) = rs.first() {
                as_sum.push(f.clone());
            } else {
                return self.const_int(0);
            };
            for r in rs.into_iter().skip(1) {
                as_sum.push(self.neg(r));
            }
            return self.add(as_sum);
        }

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
        debug_assert!(
            r.sort().is_int(),
            "`neg` needs sort Int but got {}: {}",
            r.sort(),
            r
        );
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
}

/// Some functions are commutative, so we can sort the arguments to make them easier to compare.
/// We sort to the arguments by the value of the node's id.
/// This way, we do not have "f(a, b)" and "f(b, a)" for commutative function f as separate nodes, but only one.
fn sort_commutative_args(nodes: Vec<Node>) -> Vec<Node> {
    let mut nodes = nodes;
    nodes.sort_by_key(|n| n.id);
    nodes
}
