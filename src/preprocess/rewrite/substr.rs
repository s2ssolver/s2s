use crate::node::{Node, NodeKind, NodeManager};

/// Rewrites `substr(w, s, l)` to `w[s:s+l]` if w is a constant strings and s and l are constant integers.
pub fn substr_const(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::SubStr = node.kind() {
        let w = &node.children()[0];
        let s = &node.children()[1];
        let l = &node.children()[2];
        if let NodeKind::String(ref w) = w.kind() {
            if let NodeKind::Int(s) = s.kind() {
                if let NodeKind::Int(l) = l.kind() {
                    let s = *s as usize;
                    let l = *l as usize;
                    let substr = w.chars().skip(s).take(l).collect::<String>();
                    return Some(mngr.const_str(&substr));
                }
            }
        }
    }
    None
}

/// Rewrites `at(w, s)` to `w[s]` if w is a constant strings and s is a constant integer.
/// If s is out of bounds, returns `""`.
pub fn at_const(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::At = node.kind() {
        let w = &node.children()[0];
        let s = &node.children()[1];
        if let NodeKind::String(ref w) = w.kind() {
            if let NodeKind::Int(s) = s.kind() {
                let s = *s as usize;

                match w.chars().nth(s) {
                    Some(at) => return Some(mngr.const_str(&at.to_string())),
                    None => return Some(mngr.const_str("")),
                }
            }
        }
    }
    None
}

/// Rewrites `substr(w, s, 0)` to `""` if s <= 0.
pub fn substr_negative(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::SubStr = node.kind() {
        let l = &node.children()[2];
        if let NodeKind::Int(l) = l.kind() {
            if *l <= 0 {
                return Some(mngr.const_str(""));
            }
        }
    }
    None
}

/// Rewrites `at(w, s)` to `""` if s < 0.
pub fn at_negative(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if let NodeKind::At = node.kind() {
        let s = &node.children()[1];
        if let NodeKind::Int(s) = s.kind() {
            if *s < 0 {
                return Some(mngr.const_str(""));
            }
        }
    }
    None
}
