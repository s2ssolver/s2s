use itertools::Itertools;

use crate::node::{normal::to_nnf, Node, NodeKind, NodeManager, Sorted};

/// ITE c t e ==> c -> t /\ !c -> e
pub fn ite_bool(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::Ite {
        let ifc = &node.children()[0];
        if ifc.sort().is_bool() {
            let then = &node.children()[1];
            let els = &node.children()[2];

            let ltf = mngr.imp(ifc.clone(), then.clone());
            let not_ifc = mngr.not(ifc.clone());
            let nltr = mngr.imp(not_ifc, els.clone());

            let rewrt = mngr.and(vec![ltf, nltr]);

            // need to bring into NNF
            Some(to_nnf(&rewrt, mngr))
        } else {
            None
        }
    } else {
        None
    }
}

/// Pulls ite outwards.
/// P (..., ITE c t e, ...) ==> ITE c (P ..., t, ...) (P ..., e, ...)
/// This needs to be called first
pub fn ite_pull(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if node.is_bool_fun() {
        return None;
    }
    let ch = node.children();
    if let Some((p, ite)) = ch.iter().find_position(|c| *c.kind() == NodeKind::Ite) {
        let cond = &ite.children()[0];
        let then = &ite.children()[1];
        let els = &ite.children()[2];

        let mut cond_true = Vec::new();
        let mut cond_false = Vec::new();
        for i in 0..ch.len() {
            if i == p {
                cond_true.push(then.clone());
                cond_false.push(els.clone());
            } else {
                cond_true.push(ch[i].clone());
                cond_false.push(ch[i].clone());
            }
        }
        let cond_true_p = mngr.create_node(node.kind().clone(), cond_true);
        let cond_false_p = mngr.create_node(node.kind().clone(), cond_false);
        let pulled = mngr.ite(cond.clone(), cond_true_p, cond_false_p);
        log::debug!("Normalized ITE {} ==> {}", node, pulled);
        return Some(pulled);
    }
    None
}
