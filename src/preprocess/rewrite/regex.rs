use smtlib_str::re::{deriv::DerivativeBuilder, ReOp};

use crate::node::{
    utils::{reverse, PatternIterator, Symbol},
    Node, NodeKind, NodeManager,
};

/// Fold inre(w, R) with constant w and R to
/// - true if w is in the language of R
/// - false if w is not in the language of R
pub fn inre_constant_lhs(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let lhs = &node.children()[0];
        if let NodeKind::String(s) = lhs.kind() {
            if let NodeKind::Regex(re) = node.children()[1].kind() {
                if re.accepts(&s.clone()) {
                    Some(mngr.ttrue())
                } else {
                    Some(mngr.ffalse())
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// Fold inre(X, R) when R is trivial
/// - R = None then return false
/// - R = Universal then return true
pub fn inre_trivial(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let re = &node.children()[1];
        if let NodeKind::Regex(re) = re.kind() {
            if re.none().unwrap_or(false) {
                // none regex accepts no string
                return Some(mngr.ffalse());
            } else if re.universal().unwrap_or(false) {
                // universal regex accepts all strings
                return Some(mngr.ttrue());
            }
        } else {
            unreachable!("Second child of InRe node should be a regex")
        }
    }
    None
}

/// Fold inre(lhs, w) where w is a constant string to equality lhs = w
pub fn inre_equation(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let re = &node.children()[1];
        if let NodeKind::Regex(re) = re.kind() {
            if let Some(w) = re.is_constant() {
                //rewrite as equality lhs = w
                let lhs = node.children()[0].clone();
                let rhs = mngr.const_string(w);
                return Some(mngr.eq(lhs, rhs));
            }
        }
    }
    None
}

/// Removes constants prefixes from patterns in regular constraints.
/// Let $\alpha$ be a pattern and $w$ be a constant word.
///
/// - Regular constraints of the form $w\alpha \in R$ are replaced with $\alpha \in (w^{-1})R$
/// - Regular constraints of the for $\alpha w \in R$ are replaced with $\alpha \in rev((w^{-1})rev(R))$
///
/// where $(w^{-1})R$ is the regular derivative of $R$ w.r.t. $w$ and $rev(R)$ is the reverse of $R$.
pub fn inre_strip_prefix(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let mut rewritten = false;
        let mut regex = match node.children()[1].kind() {
            NodeKind::Regex(s) => s.clone(),
            _ => return None,
        };
        let mut iter = PatternIterator::new(&node.children()[0]);
        let mut deriver = DerivativeBuilder::default();
        while let Some(Symbol::Const(c)) = iter.peek() {
            rewritten = true;
            regex = deriver.deriv(&regex, c, mngr.re_builder());
            iter.next();
        }
        let node = iter.to_node(mngr)?;

        if rewritten {
            let re = mngr.create_node(NodeKind::Regex(regex), vec![]);
            let new_node = mngr.in_re(node, re);
            return Some(new_node);
        }
    }

    None
}

/// Same as inre_strip_prefix but for suffixes.
pub fn inre_strip_suffix(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let revd = reverse_in_re(node, mngr);
        let new_node = inre_strip_prefix(&revd, mngr)?;
        // reverse back the result
        let new_node = reverse_in_re(&new_node, mngr);
        Some(new_node)
    } else {
        None
    }
}

/// Reverses the pattern and the regular expression in a regular constraint.
fn reverse_in_re(node: &Node, mngr: &mut NodeManager) -> Node {
    let left = &node.children()[0];
    let left_rev = reverse(left, mngr);
    let regex = &node.children()[1];
    let regex_rev = match regex.kind() {
        NodeKind::Regex(re) => mngr.re_builder().reversed(re),
        _ => return node.clone(),
    };
    let regex_rev = mngr.create_node(NodeKind::Regex(regex_rev), vec![]);
    mngr.create_node(NodeKind::InRe, vec![left_rev, regex_rev])
}

// Rewrite "InRe(X, comp(R))" to "Not InRe(X, R)"
pub fn inre_pull_comp(node: &Node, mngr: &mut NodeManager) -> Option<Node> {
    if *node.kind() == NodeKind::InRe {
        debug_assert!(node.children().len() == 2);
        let lhs = &node.children()[0];
        let rhs = &node.children()[1];

        if let NodeKind::Regex(re) = rhs.kind() {
            if let ReOp::Comp(inner) = re.op() {
                let new_rhs = mngr.create_node(NodeKind::Regex(inner.clone()), vec![]);
                let new_node = mngr.in_re(lhs.clone(), new_rhs);
                let negated = mngr.not(new_node);
                return Some(negated);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {

    // TODO: Add  tests
}
