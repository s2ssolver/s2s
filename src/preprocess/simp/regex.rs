use smt_str::re::{deriv::DerivativeBuilder, ReOp};

use crate::ast::{
    utils::{reverse, PatternIterator, Symbol},
    Node, NodeKind, NodeManager,
};

use super::*;

/// Fold inre(w, R) with constant w and R to
/// - true if w is in the language of R
/// - false if w is not in the language of R
#[derive(Debug, Clone, Copy)]
pub(super) struct InReConstantLhs;
impl EquivalenceRule for InReConstantLhs {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            if let NodeKind::String(s) = lhs.kind() {
                if let NodeKind::Regex(re) = node.children()[1].kind() {
                    return if re.accepts(&s.clone()) {
                        Some(mngr.ttrue())
                    } else {
                        Some(mngr.ffalse())
                    };
                }
            }
        }
        None
    }
}

/// Fold inre(X, R) when R is trivial
/// - R = None then return false
/// - R = Universal then return true
#[derive(Debug, Clone, Copy)]
pub(super) struct InReTrivial;
impl EquivalenceRule for InReTrivial {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
}

/// Fold inre(lhs, w) where w is a constant string to equality lhs = w
#[derive(Debug, Clone, Copy)]
pub(super) struct InReEquation;
impl EquivalenceRule for InReEquation {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
}

/// Removes constants prefixes from patterns in regular constraints.
/// Let $\alpha$ be a pattern and $w$ be a constant word.
///
/// - Regular constraints of the form $w\alpha \in R$ are replaced with $\alpha \in (w^{-1})R$
/// - Regular constraints of the for $\alpha w \in R$ are replaced with $\alpha \in rev((w^{-1})rev(R))$
///
/// where $(w^{-1})R$ is the regular derivative of $R$ w.r.t. $w$ and $rev(R)$ is the reverse of $R$.
#[derive(Debug, Clone, Copy)]
pub(super) struct InReStripPrefix;
impl EquivalenceRule for InReStripPrefix {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
}

/// Same as inre_strip_prefix but for suffixes.
#[derive(Debug, Clone, Copy)]
pub(super) struct InReStripSuffix;
impl EquivalenceRule for InReStripSuffix {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        if *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let revd = reverse_in_re(node, mngr);
            if let Some(new_node) = InReStripPrefix.apply(&revd, asserted, mngr) {
                let new_node = reverse_in_re(&new_node, mngr);
                return Some(new_node);
            }
            // reverse back the result
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

/// Rewrite "InRe(X, comp(R))" to "Not InRe(X, R)"
#[derive(Debug, Clone, Copy)]
pub(super) struct InRePullComp;
impl EquivalenceRule for InRePullComp {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
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
}

/// Finds constant prefixes and suffixes of entailed regular constraints on variables.
/// That means, it derives the following substitutions:
///
/// - if `x \in wR` then  x -> wx
/// - if `x \in Rw` then  x -> xw
///
/// This interplays with [ConstantDerivation], which will subsequently strip the constant from the variable by using derivatives on the regular expressions or reduces the constant prefix/suffix constraints.
#[derive(Clone, Default, Debug)]
pub(super) struct ConstantPrefixSuffix;

impl EntailmentRule for ConstantPrefixSuffix {
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        _: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution> {
        // This is only applicable if the node itself is asserted
        if !asserted.contains(node) {
            return None;
        }

        if node.is_atomic() && *node.kind() == NodeKind::InRe {
            debug_assert!(node.children().len() == 2);
            let lhs = &node.children()[0];
            if let NodeKind::Variable(v) = &lhs.kind() {
                if let NodeKind::Regex(regex) = &node.children()[1].kind() {
                    if let Some(pre) = regex.prefix().filter(|p| !p.is_empty()) {
                        // X -> preX
                        let prefix_w = mngr.const_string(pre);
                        let pattern = mngr.concat(vec![prefix_w, lhs.clone()]);

                        let mut subst = VarSubstitution::default();
                        subst.add(v.clone(), pattern);
                        return Some(subst);
                    } else if let Some(suf) = regex.suffix().filter(|s| !s.is_empty()) {
                        // X -> Xsuf
                        let suffix_w = mngr.const_string(suf);
                        let pattern = mngr.concat(vec![lhs.clone(), suffix_w]);

                        let mut subst = VarSubstitution::default();
                        subst.add(v.clone(), pattern);
                        return Some(subst);
                    }
                } else {
                    unreachable!("Expected a regex node");
                }
            }
        }
        None
    }
}
