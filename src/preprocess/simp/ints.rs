use std::{collections::HashSet, rc::Rc};

use crate::node::{NodeKind, Sorted, Variable};

use super::*;

/// Finds asserted terms of the form `L = 0` or `L <= 0`, where
/// all terms in L are of the form c|x| with c>0
/// and returns `x = epsilon` for all c|x| in L.`
#[derive(Clone, Default)]
pub struct ZeroLengthEpsilon;

impl ZeroLengthEpsilon {
    fn apply(lhs: &Node, mngr: &mut NodeManager) -> Option<Simplification> {
        // Collects all in the given node of sort string that need to be replaced by epsilon
        // Returns false if a variable is found that is not of sort string
        fn collect_vars(n: &Node, in_len: bool, vars: &mut HashSet<Rc<Variable>>) -> bool {
            match n.kind() {
                NodeKind::Length => {
                    assert!(!in_len);
                    for c in n.children() {
                        // must be true since the length of a string is a string
                        collect_vars(c, true, vars);
                    }
                    true
                }
                NodeKind::Concat => {
                    assert!(in_len);
                    for c in n.children() {
                        // must be true since we can only concatenate strings
                        collect_vars(c, in_len, vars);
                    }
                    true
                }
                NodeKind::Variable(v) if in_len => {
                    // must be a string, we are in a length
                    assert!(v.sort().is_string());
                    vars.insert(v.clone());
                    true
                }
                NodeKind::Mul | NodeKind::Add => {
                    assert!(!in_len);
                    for c in n.children() {
                        if !collect_vars(c, in_len, vars) {
                            // If we find a variable that is not of sort string, we can't apply the rule
                            // and return false
                            return false;
                        }
                    }
                    true
                }
                NodeKind::Int(i) => *i >= 0, // if we find a negative integer, we can't apply the rule
                NodeKind::Sub => return false,
                NodeKind::Variable(v) => {
                    debug_assert!(!in_len);
                    debug_assert!(v.sort().is_int());
                    // if we find a variable that is not of sort string, we can't apply the rule
                    return false;
                }
                _ => return false,
            }
        }
        let mut vars = HashSet::new();
        if collect_vars(lhs, false, &mut vars) {
            let mut subs = NodeSubstitution::default();
            let epsi = mngr.const_str("");
            for v in vars {
                subs.add(v, epsi.clone());
            }
            Some(Simplification::new(subs, None))
        } else {
            None
        }
    }
}

impl SimpRule for ZeroLengthEpsilon {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed {
            match node.kind() {
                NodeKind::Eq => {
                    debug_assert!(node.children().len() == 2);
                    let lhs = node.children().first().unwrap();
                    let rhs = node.children().last().unwrap();
                    if lhs.sort().is_int() && rhs.sort().is_int() {
                        match (lhs.kind(), rhs.kind()) {
                            (_, NodeKind::Int(0)) => ZeroLengthEpsilon::apply(lhs, mngr),
                            (NodeKind::Int(0), _) => ZeroLengthEpsilon::apply(rhs, mngr),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                NodeKind::Le => {
                    debug_assert!(node.children().len() == 2);
                    let lhs = node.children().first().unwrap();
                    let rhs = node.children().last().unwrap();
                    match (lhs.kind(), rhs.kind()) {
                        (_, NodeKind::Int(0)) => ZeroLengthEpsilon::apply(lhs, mngr),
                        _ => None,
                    }
                }
                NodeKind::Ge => {
                    debug_assert!(node.children().len() == 2);
                    let lhs = node.children().first().unwrap();
                    let rhs = node.children().last().unwrap();
                    match (lhs.kind(), rhs.kind()) {
                        (NodeKind::Int(0), _) => ZeroLengthEpsilon::apply(rhs, mngr),
                        _ => None,
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn name(&self) -> &str {
        "ZeroLengthEpsilon"
    }
}
