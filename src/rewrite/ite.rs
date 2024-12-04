use crate::node::{normal::to_nnf, Node, NodeKind, NodeManager, Sorted};

use super::RewriteRule;

pub struct IteRewrite;

impl RewriteRule for IteRewrite {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
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
}
