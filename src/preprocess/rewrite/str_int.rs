use crate::node::{Node, NodeKind, NodeManager};

pub fn to_int_constant(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::ToInt = *node.kind() {
        let ch = node.children().first().unwrap();
        if let Some(s) = ch.as_str_const() {
            if s.is_empty() {
                return Some(mngr.const_int(-1));
            }
            let i = match i64::from_str_radix(s, 10) {
                Ok(i) => i,
                Err(_) => -1,
            };
            return Some(mngr.const_int(i));
        }
    }
    None
}

pub fn from_int_constant(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::FromInt = *node.kind() {
        let ch = node.children().first().unwrap();
        if let Some(i) = ch.as_int_const() {
            if i >= 0 {
                return Some(mngr.const_str(&i.to_string()));
            } else {
                return Some(mngr.const_str(""));
            }
        }
    }
    None
}
