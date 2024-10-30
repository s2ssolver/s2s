use regulaer::re::{deriv::Deriver, RegexProps};

use crate::node::{
    utils::{reverse, Symbol, SymbolIterator},
    Node, NodeKind, NodeManager,
};

use super::RewriteRule;

pub struct FoldConstantRegex;

impl RewriteRule for FoldConstantRegex {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            if let NodeKind::Regex(re) = node.children()[1].kind() {
                if re.is_none().unwrap_or(false) {
                    // none regex accepts no string
                    return Some(mngr.ffalse());
                } else if re.is_universal().unwrap_or(false) {
                    // universal regex accepts all strings
                    return Some(mngr.ttrue());
                } else if let Some(w) = re.is_constant() {
                    //rewrite as equality lhs = w
                    let lhs = node.children()[0].clone();
                    let rhs = mngr.const_string(w.iter().collect());
                    return Some(mngr.eq(lhs, rhs));
                }
            } else {
                unreachable!("Second child of InRe node should be a regex")
            }
        }
        None
    }
}

pub struct FoldConstantInRe;

impl RewriteRule for FoldConstantInRe {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let pattern = &node.children()[0];
            if let NodeKind::String(s) = pattern.kind() {
                if let NodeKind::Regex(re) = node.children()[1].kind() {
                    if re.accepts(&s.clone().into()) {
                        return Some(mngr.ttrue());
                    } else {
                        return Some(mngr.ffalse());
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
}

/// Removes constants prefixes and suffixes of patterns in regular constraints.
/// Let $\alpha$ be a pattern and $w$ be a constant word.
/// - Regular constraints of the form $w\alpha \in R$ are replaced with $\alpha \in (w^{-1})R$
/// - Regular constraints of the for $\alpha w \in R$ are replaced with $\alpha \in rev((w^{-1})rev(R))$
/// where $(w^{-1})R$ is the regular derivative of $R$ w.r.t. $w$ and $rev(R)$ is the reverse of $R$.
pub struct ReStripConstantPrefix;
impl RewriteRule for ReStripConstantPrefix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let mut rewritten = false;
            let mut regex = match node.children()[1].kind() {
                NodeKind::Regex(s) => s.clone(),
                _ => return None,
            };
            let mut iter = SymbolIterator::new(&node.children()[0]);
            let mut deriver = Deriver::default();
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

pub struct ReStripConstantSuffix;

impl RewriteRule for ReStripConstantSuffix {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let revd = reverse_in_re(node, mngr);
            let new_node = ReStripConstantPrefix.apply(&revd, mngr)?;
            // reverse back the result
            let new_node = reverse_in_re(&new_node, mngr);
            Some(new_node)
        } else {
            None
        }
    }
}
