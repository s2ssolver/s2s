use crate::node::{Node, NodeKind, NodeManager};

/// Idempency of replacement operation.
/// - `replace(x, y, y) = x`
/// - `replace_all(x, y, y) = x`
pub fn replace_idem(node: &Node, _: &mut NodeManager) -> Option<Node> {
    match node.kind() {
        NodeKind::Replace | NodeKind::ReplaceAll => {
            debug_assert_eq!(node.children().len(), 3);
            let from = node.children()[1].clone();
            let to = node.children()[2].clone();
            if from == to {
                return Some(node.children()[0].clone());
            }
        }
        _ => {}
    }
    None
}
