use regulaer::re::RegexProps;

use crate::node::NodeKind;

use super::*;

/// Finds constant prefixes and suffixes of entailed regular constraints on variables.
/// That means, it derives the following substitutions:
/// - if `x \in wR` then  x -> wx
/// - if `x \in Rw` then  x -> xw
/// This interplays with [ConstantDerivation], which will subsequently strip the constant from the variable by using derivatives on the regular expressions or reduces the constant prefix/suffix constraints.
#[derive(Clone, Default)]
pub struct ConstantPrefixSuffix;

impl SimpRule for ConstantPrefixSuffix {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        if entailed && node.is_atomic() {
            if *node.kind() == NodeKind::InRe {
                debug_assert!(node.children().len() == 2);
                let lhs = &node.children()[0];
                if let NodeKind::Variable(_) = &lhs.kind() {
                    if let NodeKind::Regex(regex) = &node.children()[1].kind() {
                        if let Some(pre) = regex.prefix().filter(|p| !p.is_empty()) {
                            // X -> preX
                            let as_string = pre.iter().collect::<String>();
                            debug_assert!(as_string.len() == pre.len());
                            let prefix_w = mngr.const_string(as_string);
                            let pattern = mngr.concat(vec![prefix_w, lhs.clone()]);

                            let mut subst = NodeSubstitution::default();
                            subst.add(lhs.clone(), pattern, mngr);
                            return Some(subst.into());
                        } else if let Some(suf) = regex.suffix().filter(|s| !s.is_empty()) {
                            // X -> Xsuf
                            let as_string = suf.iter().collect::<String>();
                            debug_assert!(as_string.len() == suf.len());
                            let suffix_w = mngr.const_string(as_string);
                            let pattern = mngr.concat(vec![lhs.clone(), suffix_w]);

                            let mut subst = NodeSubstitution::default();
                            subst.add(lhs.clone(), pattern, mngr);
                            return Some(subst.into());
                        }
                    } else {
                        unreachable!("Expected a regex node");
                    }
                }
            }
        }
        None
    }

    fn name(&self) -> &str {
        "RegexConstantPrefixSuffix"
    }
}
