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
        fn collect_vars(n: &Node, in_len: bool, vars: &mut HashSet<Rc<Variable>>) -> bool {
            match n.kind() {
                NodeKind::Length => {
                    assert!(!in_len);
                    for c in n.children() {
                        collect_vars(c, true, vars);
                    }
                }
                NodeKind::Concat => {
                    assert!(in_len);
                    for c in n.children() {
                        collect_vars(c, in_len, vars);
                    }
                }
                NodeKind::Variable(v) if in_len => {
                    assert!(v.sort().is_string());
                    vars.insert(v.clone());
                }
                NodeKind::Mul | NodeKind::Add => {
                    assert!(!in_len);
                    for c in n.children() {
                        collect_vars(c, in_len, vars);
                    }
                }
                NodeKind::Int(i) => {
                    if *i < 0 {
                        return false;
                    }
                }
                NodeKind::Sub => return false,
                NodeKind::Variable(_) => return false,
                _ => return false,
            }
            true
        }
        let mut vars = HashSet::new();
        if collect_vars(lhs, false, &mut vars) {
            let mut subs = NodeSubstitution::default();
            let epsi = mngr.const_str("");
            for v in vars {
                let asnode = mngr.var(v);
                subs.add(asnode, epsi.clone(), mngr);
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
                NodeKind::Eq if node.sort().is_int() => {
                    debug_assert!(node.children().len() == 2);
                    let lhs = node.children().first().unwrap();
                    let rhs = node.children().last().unwrap();
                    match (lhs.kind(), rhs.kind()) {
                        (_, NodeKind::Int(0)) => ZeroLengthEpsilon::apply(lhs, mngr),
                        (NodeKind::Int(0), _) => ZeroLengthEpsilon::apply(rhs, mngr),
                        _ => None,
                    }
                }
                NodeKind::Le => {
                    debug_assert!(node.children().len() == 2);
                    let lhs = node.children().first().unwrap();
                    let rhs = node.children().last().unwrap();
                    match (lhs.kind(), rhs.kind()) {
                        (_, NodeKind::Int(0)) => ZeroLengthEpsilon::apply(lhs, mngr),
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
