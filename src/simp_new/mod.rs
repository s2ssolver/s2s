mod entailed;
mod independent;
mod ints;
mod levis;
mod reprefix;

use crate::node::{Node, NodeManager, NodeSubstitution};

/// A simplification inferred by a simplification rule.
/// Consists of a node substitution `h` and an optional entailment `n`.
/// The simplification is applied to the formula by computing `h(F) /\ n`.
pub struct Simplification {
    subs: NodeSubstitution,
    entails: Option<Node>,
}

impl Simplification {
    /// Create a new simplification.
    pub fn new(subs: NodeSubstitution, entails: Option<Node>) -> Self {
        Simplification { subs, entails }
    }

    /// Get the node substitution.
    pub fn substitution(&self) -> &NodeSubstitution {
        &self.subs
    }

    /// Get the entailment.
    pub fn entailment(&self) -> Option<&Node> {
        self.entails.as_ref()
    }
}

impl From<NodeSubstitution> for Simplification {
    fn from(subs: NodeSubstitution) -> Self {
        Simplification::new(subs, None)
    }
}

/// A simplification rule.
/// A simplification rule is a function that takes a node and returns a substitution that is applied globally.
/// As such, it must be satisfiability preserving.
pub trait SimpRule {
    /// Apply the simplification rule to the given node.
    /// If the rule applies, then return the new node.
    /// If the rule does not apply, then return None.
    /// The `entailed` flag indicates whether the node is entailed by the formula, i.e., if it is the root or reachable from the root by only following conjunctions.
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification>;
}
