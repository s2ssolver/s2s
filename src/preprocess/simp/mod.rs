//! Simplification module
//!

mod boolean;
mod elim;
mod entailed;
mod factors;
mod fwd;
mod independent;
mod int;
pub mod levis;
mod regex;
mod replace;
mod str_int;
mod strlen;
mod substr;
mod weq;

use std::fmt::Debug;

use elim::EliminateEntailed;
use indexmap::{IndexMap, IndexSet};

use crate::node::{get_entailed, Node, NodeKind, NodeManager, VarSubstitution};

/// A rewrite rule that can be applied to a node locally.
/// It returns a new node if the rule applies, or None if it does not.
/// The new node **must** be logically equivalent to the original node and **should** be 'simpler' than the original node.
trait EquivalenceRule: Debug {
    /// Apply the rewrite rule to the given node.
    /// Returns a either a new node or [None] if the rule does not apply.
    /// The new node is simplified and logically equivalent to the original node.
    ///
    /// Additionally, the simplifier passes the set of currenly asserted nodes to the rule.
    /// The facts are the nodes that must be true for the current node to be true.
    fn apply(&self, node: &Node, facts: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node>;
}

/// A rewrite rule that infers a substitution from the given node, that can be applied globally.
/// Globally means that the substitution is applied to the entire AST, not just the current node.
/// After application, the resulting formula must be equisatisfiable to the original formula.
/// More over, if `h` is a substitution applied to the formula `f`, and `h(f)` has a solution `g`,
/// then `h.g` must also be a solution to `f`.
trait EntailmentRule: Debug {
    /// Infer a globally valid [VarSubstitution] from the given node.
    /// The substitution is applied to the entire AST, not just the current node.
    /// If the rule does not apply, it returns [None].
    ///
    /// The rule is passed the current node, the set of asserted nodes, and the polarity of the node.
    /// The polarity is true if the node is positive, and false if it is negative.
    /// The list of asserted nodes is the set of nodes that must be true for the current node to be true.
    fn apply(
        &self,
        node: &Node,
        facts: &IndexSet<Node>,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution>;

    /// Initialize the rule with the given node manager and root node of the AST.
    /// This is always called before every call to [apply].
    fn init(&mut self, _root: &Node, _mngr: &mut NodeManager) {}
}

pub struct SimpResult {
    /// The simplified node
    pub node: Node,
    /// The substitutions that have been applied to the root node.
    pub subs: Vec<VarSubstitution>,
}

/// The simplifier performs simplification of the AST by applying equivalence and entailment rules.
/// If performs multiple passes over the AST, applying the rules in a predefined order.
/// After each pass, it checks if the AST has changed.
/// If it has, it continues to apply the rules until no more changes are made or the maximum number of passes is reached.
///
/// After termination, the simplifier returns the simplified AST.
/// The simplified AST is logically equisatifiable to the original AST.
/// It also keeps track of the substitutions that have been applied to the root node.
/// If the simplified formula has a solution, the substitutions can be used to find a solution for the original formula.
pub struct Simplifier {
    equiv_rules: Vec<Box<dyn EquivalenceRule>>,
    entail_rules: Vec<Box<dyn EntailmentRule>>,
    rewrite_cache: IndexMap<Node, Node>,

    /// Substitutions that have been applied to the root node.
    applied_subs: Vec<VarSubstitution>,
}

impl Simplifier {
    /// Apply the simplifier to the given node.
    /// The simplifier performs at most `max_passes` passes over the node.
    /// It returns a [SimpResult] containing the simplified node and the substitutions that have been applied to the root node.
    pub fn apply(mut self, node: &Node, max_passes: usize, mngr: &mut NodeManager) -> SimpResult {
        let mut current = node.clone();

        let mut last_size = current.size();
        let mut pass = 0;

        while pass < max_passes || current.size() < last_size {
            match self.pass(&current, mngr) {
                Some(rw) => {
                    current = rw;
                }
                None => {
                    break;
                }
            }
            if current.size() >= last_size {
                // we only count passes if we did not simplify
                pass += 1;
            }
            last_size = current.size();
        }

        let subs = self.applied_subs;
        SimpResult {
            node: current,
            subs,
        }
    }

    /// Perform a rewrite pass over the given node.
    /// This method applies the rules in the order they were added to the rewriter.
    /// It first applies the rules to the children of the node and then to the node itself.
    /// A single pass calls every rule once for every node in the AST.
    fn pass(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        // First remove all non-entailed occurrences of entailed literals
        // This is neither a EquivalenceRule nor an EntailmentRule, but a simplification step that we do first.
        // If a literal is entailed, then this replaces all other occurrences of the literal with `true`.
        let mut lit_eliminator = EliminateEntailed::default();

        // Clear the cache for the current pass
        // Otherwise we might miss some rewrites
        self.rewrite_cache.clear();

        let mut simped_node = lit_eliminator.apply(node, mngr);

        // Apply equivalence rules
        let mut applied = false;
        simped_node = match self.pass_equivalence(&simped_node, &Vec::new(), mngr) {
            Some(rw) => {
                applied = true;
                rw
            }
            None => node.clone(),
        };

        // Apply entailment rules
        if let Some(rw) = self.pass_entailment(&simped_node, mngr) {
            applied = true;
            simped_node = rw;
        }

        if applied {
            Some(simped_node)
        } else {
            None
        }
    }

    fn pass_equivalence(
        &mut self,
        node: &Node,
        path: &[&Node],
        mngr: &mut NodeManager,
    ) -> Option<Node> {
        if let Some(rw) = self.rewrite_cache.get(node) {
            return Some(rw.clone());
        }

        // Apply to children
        let mut applied_children = Vec::with_capacity(node.children().len());
        let mut applied = false;

        let mut path_ch = path.to_vec();
        path_ch.push(node);

        for child in node.children() {
            match self.pass_equivalence(child, &path_ch, mngr) {
                Some(new_child) => {
                    applied_children.push(new_child.clone());
                    applied = true;
                }
                None => applied_children.push(child.clone()),
            }
        }

        // Apply all rules to node
        let mut new_node = if applied {
            mngr.create_node(node.kind().clone(), applied_children)
        } else {
            node.clone()
        };

        /// Returns all nodes that must be true for the current node to be true.
        fn get_asserted(path: &[&Node]) -> IndexSet<Node> {
            let mut asserted = IndexSet::new();
            if path.len() == 1 {
                // if the node is a leaf, we need to add it to the asserted set
                asserted.insert(path[0].clone());
            }
            for &node in path.iter() {
                if *node.kind() == NodeKind::And {
                    asserted.insert(node.clone());
                }
            }
            asserted
        }

        let facts = get_asserted(path);
        // remove self from the asserted set, otherwise we might get unsound results.
        // we dont with this approach?
        // asserted.remove(node);

        for rule in self.equiv_rules.iter() {
            if let Some(rw) = rule.apply(&new_node, &facts, mngr) {
                log::debug!("({:?}) {} ==> {}", rule, new_node, rw);
                new_node = rw;
                applied = true;
            }
        }
        // Also cache if not applied to not traverse the same node again
        self.rewrite_cache.insert(node.clone(), new_node.clone());

        if applied {
            Some(new_node)
        } else {
            None
        }
    }

    fn pass_entailment(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        fn find_subs(
            rules: &mut [Box<dyn EntailmentRule>],
            node: &Node,
            asserted: &IndexSet<Node>,
            pol: bool,
            mngr: &mut NodeManager,
        ) -> Option<VarSubstitution> {
            for rule in rules.iter_mut() {
                if let Some(sub) = rule.apply(node, asserted, pol, mngr) {
                    if !sub.is_identity() && !sub.is_empty() {
                        log::debug!("({:?}) inferred {}", rule, sub);
                        return Some(sub);
                    }
                }
            }

            let pol = match node.kind() {
                NodeKind::Not => !pol,
                _ => pol,
            };

            for child in node.children() {
                if let Some(sub) = find_subs(rules, child, asserted, pol, mngr) {
                    return Some(sub);
                }
            }

            None
        }

        let mut applied = false;
        let mut new_node = node.clone();
        // initialize the rules with the current node
        for rule in self.entail_rules.iter_mut() {
            rule.init(node, mngr);
        }
        let mut facts = get_entailed(&new_node);
        while let Some(sub) = find_subs(&mut self.entail_rules, &new_node, &facts, true, mngr) {
            new_node = sub.apply(&new_node, mngr);

            self.applied_subs.push(sub);
            applied = true;
            // reinitialize the rules with the new node
            for rule in self.entail_rules.iter_mut() {
                rule.init(&new_node, mngr);
            }
            // update the asserted set
            facts = get_entailed(&new_node);
        }

        if applied {
            Some(new_node)
        } else {
            None
        }
    }
}

impl Default for Simplifier {
    fn default() -> Self {
        let equiv_rules: Vec<Box<dyn EquivalenceRule>> = vec![
            Box::new(boolean::OrAssocFlatten),
            Box::new(boolean::AndAssocFlatten),
            Box::new(boolean::AndConst),
            Box::new(boolean::AndIdem),
            Box::new(boolean::AndComp),
            Box::new(boolean::OrConst),
            Box::new(boolean::OrIdem),
            Box::new(boolean::OrComp),
            Box::new(boolean::NotConst),
            Box::new(boolean::NotDoubleNegation),
            Box::new(boolean::EqualityTrivial),
            Box::new(regex::InReConstantLhs),
            Box::new(regex::InReTrivial),
            Box::new(regex::InReEquation),
            Box::new(regex::InReStripPrefix),
            Box::new(regex::InReStripSuffix),
            Box::new(regex::InRePullComp),
            Box::new(int::FoldConstantInts),
            Box::new(int::LessTrivial),
            Box::new(int::GreaterTrivial),
            Box::new(int::EqualityTrivial),
            Box::new(int::DistributeNeg),
            // does not seem to help
            Box::new(int::NormalizeIneq),
            Box::new(int::NotComparison),
            Box::new(fwd::LinIntForward),
            Box::new(strlen::StringLengthAddition),
            Box::new(strlen::ConstStringLength),
            Box::new(strlen::LengthTrivial),
            Box::new(strlen::TrivialLenghtConstraints),
            // Hurts forward reasoning
            //Box::new(strlen::LengthToReg),
            Box::new(weq::ConstMismatch),
            Box::new(weq::StripLCP),
            Box::new(weq::StripLCS),
            Box::new(weq::LengthReasoning),
            Box::new(weq::ParikhMatrixMismatch),
            Box::new(factors::TrivialPrefixof),
            Box::new(factors::TrivialSuffixof),
            Box::new(factors::TrivialContains),
            Box::new(factors::FactorOfEmptyString),
            Box::new(substr::SubstrConst),
            Box::new(substr::SubstrNegative),
            Box::new(substr::AtNegative),
            Box::new(substr::AtConst),
            Box::new(replace::ReplaceIdem),
            Box::new(replace::ReplaceInEpsilon),
            Box::new(replace::ReplaceSelf),
            Box::new(replace::ReplaceEpsilon),
            Box::new(str_int::ToIntConstant),
            Box::new(str_int::FromIntConstant),
            Box::new(str_int::VarEqConstantToInt),
        ];

        /* Entailment rules */
        let entail_rules: Vec<Box<dyn EntailmentRule>> = vec![
            Box::new(regex::ConstantPrefixSuffix),
            Box::new(independent::IndependentVariableAssignment::default()),
            Box::new(strlen::ZeroLengthEpsilon),
            Box::new(levis::LevisRule),
            Box::new(entailed::EntailedBooleanVars),
            Box::new(entailed::EntailedAssigments),
        ];

        Simplifier {
            equiv_rules,
            entail_rules,
            rewrite_cache: IndexMap::new(),
            applied_subs: Vec::new(),
        }
    }
}
