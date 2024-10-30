use regulaer::re::{deriv::deriv_word, Word};

use crate::node::{Node, NodeKind, NodeManager};

use super::RewriteRule;

/// Removes constants prefixes and suffixes of patterns in regular constraints.
/// Let $\alpha$ be a pattern and $w$ be a constant word.
/// - Regular constraints of the form $w\alpha \in R$ are replaced with $\alpha \in (w^{-1})R$
/// - Regular constraints of the for $\alpha w \in R$ are replaced with $\alpha \in rev((w^{-1})rev(R))$
/// where $(w^{-1})R$ is the regular derivative of $R$ w.r.t. $w$ and $rev(R)$ is the reverse of $R$.
pub struct ReStripConstant;
impl RewriteRule for ReStripConstant {
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let mut pattern = mngr.patternize(&node.children()[0])?.as_ref().clone();
            let mut regex = match node.children()[1].kind() {
                NodeKind::Regex(s) => s.clone(),
                _ => return None,
            };
            let mut rewritten = false;
            let prefix = pattern.constant_prefix();
            if !prefix.is_empty() {
                rewritten = true;
                pattern = pattern.strip_prefix(prefix.len());
                regex = deriv_word(&regex, &prefix.into(), mngr.re_builder())
            };
            let suffix = pattern.constant_suffix();
            if !suffix.is_empty() {
                rewritten = true;
                let suffix: Word = suffix.into();
                let suffix_rev = suffix.reversed();
                pattern = pattern.strip_suffix(suffix_rev.len());
                let regex_rev = mngr.re_builder().reversed(&regex);
                let regex_rev_derived =
                    deriv_word(&regex_rev, &suffix_rev.into(), mngr.re_builder());
                // reverse back the derivative
                regex = mngr.re_builder().reversed(&regex_rev_derived);
            };

            if rewritten {
                let node_lhs = mngr.depatternize(&pattern);
                let node_rhs = mngr.create_node(NodeKind::Regex(regex), vec![]);
                let new_node = mngr.create_node(NodeKind::InRe, vec![node_lhs, node_rhs]);
                return Some(new_node);
            }
        }

        None
    }
}
