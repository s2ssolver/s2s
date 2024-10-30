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

impl Into<(NodeSubstitution, Option<Node>)> for Simplification {
    fn into(self) -> (NodeSubstitution, Option<Node>) {
        (self.subs, self.entails)
    }
}

pub struct Simplifier {
    rules: Vec<SimpRules>,
    /// Substitutions that were applied globally in the order they were applied.
    substitutions: Vec<NodeSubstitution>,
}

impl Default for Simplifier {
    fn default() -> Self {
        Simplifier {
            rules: vec![
                SimpRules::entailed_boolean_vars(),
                SimpRules::entailed_assignments(),
                SimpRules::remove_entailed(),
                SimpRules::independent_variable_assignment(),
                SimpRules::zero_length_epsilon(),
                SimpRules::levis_weq(),
                SimpRules::constant_prefix_suffix(),
            ],
            substitutions: Vec::new(),
        }
    }
}

impl Simplifier {
    pub fn simplify(&mut self, node: &Node, passes: usize, mngr: &mut NodeManager) -> Option<Node> {
        self.substitutions.clear();
        let mut result = None;
        for _ in 0..passes {
            let current = result.as_ref().unwrap_or_else(|| node);
            if let Some(simp) = self.apply(node, true, mngr) {
                let (subs, entailed) = simp.into();
                let mut applied = subs.apply(current, mngr);
                self.substitutions.push(subs);
                if let Some(entailed) = entailed {
                    applied = mngr.and(vec![applied, entailed]);
                }
                result = Some(applied);
            } else {
                // No simplification was found.
                break;
            }
        }
        result
    }

    fn apply(
        &mut self,
        node: &Node,
        entailed: bool,
        mngr: &mut NodeManager,
    ) -> Option<Simplification> {
        // Check if any simplifier applies to this node.
        // If so, then return the simplification.
        for rule in &mut self.rules {
            if let Some(simplification) = rule.apply(node, entailed, mngr) {
                return Some(simplification);
            }
        }
        // Else, descend into the children.
        for child in node.children() {
            if let Some(simplification) = self.apply(child, false, mngr) {
                return Some(simplification);
            }
        }
        // No simplification was found.
        None
    }

    /// Get the substitutions that were applied globally in the order they were applied.
    pub fn applied(&self) -> &[NodeSubstitution] {
        &self.substitutions
    }
}

#[derive(Clone)]
enum SimpRules {
    /* Entailments */
    EntailedBooleanVars(entailed::EntailedBooleanVars),
    EntailedAssigments(entailed::EntailedAssigments),
    RemoveEntailed(entailed::RemoveEntailed),
    /* Independet Variables */
    IndependentVariableAssignment(independent::IndependentVariableAssignment),

    /* Length Reasoning */
    ZeroLengthEpsilon(ints::ZeroLengthEpsilon),

    /* Weq Reasoning */
    LevisWeq(levis::LevisWeq),

    /* Regular Expression Reasoning */
    ConstantPrefixSuffix(reprefix::ConstantPrefixSuffix),
}

impl SimpRules {
    pub fn entailed_boolean_vars() -> Self {
        SimpRules::EntailedBooleanVars(entailed::EntailedBooleanVars::default())
    }

    pub fn entailed_assignments() -> Self {
        SimpRules::EntailedAssigments(entailed::EntailedAssigments::default())
    }

    pub fn remove_entailed() -> Self {
        SimpRules::RemoveEntailed(entailed::RemoveEntailed::default())
    }

    pub fn independent_variable_assignment() -> Self {
        SimpRules::IndependentVariableAssignment(
            independent::IndependentVariableAssignment::default(),
        )
    }

    pub fn zero_length_epsilon() -> Self {
        SimpRules::ZeroLengthEpsilon(ints::ZeroLengthEpsilon::default())
    }

    pub fn levis_weq() -> Self {
        SimpRules::LevisWeq(levis::LevisWeq::default())
    }

    pub fn constant_prefix_suffix() -> Self {
        SimpRules::ConstantPrefixSuffix(reprefix::ConstantPrefixSuffix::default())
    }

    fn as_mut(&mut self) -> &mut dyn SimpRule {
        match self {
            SimpRules::EntailedBooleanVars(rule) => rule,
            SimpRules::EntailedAssigments(rule) => rule,
            SimpRules::RemoveEntailed(rule) => rule,
            SimpRules::IndependentVariableAssignment(rule) => rule,
            SimpRules::ZeroLengthEpsilon(rule) => rule,
            SimpRules::LevisWeq(rule) => rule,
            SimpRules::ConstantPrefixSuffix(rule) => rule,
        }
    }

    fn as_ref(&self) -> &dyn SimpRule {
        match self {
            SimpRules::EntailedBooleanVars(rule) => rule,
            SimpRules::EntailedAssigments(rule) => rule,
            SimpRules::RemoveEntailed(rule) => rule,
            SimpRules::IndependentVariableAssignment(rule) => rule,
            SimpRules::ZeroLengthEpsilon(rule) => rule,
            SimpRules::LevisWeq(rule) => rule,
            SimpRules::ConstantPrefixSuffix(rule) => rule,
        }
    }
}

/// A simplification rule.
/// A simplification rule is a function that takes a node and returns a substitution that is applied globally.
/// As such, it must be satisfiability preserving.
trait SimpRule {
    /// Apply the simplification rule to the given node.
    /// If the rule applies, then return the new node.
    /// If the rule does not apply, then return None.
    /// The `entailed` flag indicates whether the node is entailed by the formula, i.e., if it is the root or reachable from the root by only following conjunctions.
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification>;

    fn init(&mut self, _root: &Node) {}
}

impl SimpRule for SimpRules {
    fn apply(&self, node: &Node, entailed: bool, mngr: &mut NodeManager) -> Option<Simplification> {
        self.as_ref().apply(node, entailed, mngr)
    }

    fn init(&mut self, root: &Node) {
        self.as_mut().init(root);
    }
}
