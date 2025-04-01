/// Rewrite rules for transforming Boolean nodes.
mod boolean;
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

use indexmap::{IndexMap, IndexSet};

use crate::node::{get_entailed, Node, NodeKind, NodeManager, VarSubstitution};

/// A rewrite rule that can be applied to a node.
trait EquivalenceRule: Debug {
    /// Apply the rewrite rule to the given node.
    /// Returns a [RewriteResult] indicating the result of the rewrite.
    /// If the rules does not apply, it should return [None].
    fn apply(&self, node: &Node, asserted: &IndexSet<Node>, mngr: &mut NodeManager)
        -> Option<Node>;
}

trait EntailmentRule: Debug {
    /// Apply the rewrite rule to the given node.
    /// Returns a [RewriteResult] indicating the result of the rewrite.
    /// If the rules does not apply, it should return [None].
    fn apply(
        &self,
        node: &Node,
        asserted: &IndexSet<Node>,
        pol: bool,
        mngr: &mut NodeManager,
    ) -> Option<VarSubstitution>;

    /// Initialize the rule with the given node manager and root node.
    /// The root node is the entry point for the entailed rules, and not necessarily the root of the AST.
    fn init(&mut self, _root: &Node, _mngr: &mut NodeManager) {}
}

pub struct Rewriter {
    equiv_rules: Vec<Box<dyn EquivalenceRule>>,
    entail_rules: Vec<Box<dyn EntailmentRule>>,
    rewrite_cache: IndexMap<Node, Node>,

    /// Substitutions that have been applied to the root node.
    applied_subs: Vec<VarSubstitution>,
}

impl Rewriter {
    pub fn rewrite(&mut self, node: &Node, max_passes: usize, mngr: &mut NodeManager) -> Node {
        self.applied_subs.clear();
        let mut current = node.clone();
        for _ in 0..max_passes {
            match self.pass(&current, mngr) {
                Some(rw) => {
                    current = rw;
                }
                None => {
                    break;
                }
            }
        }

        current
    }

    /// Get the substitutions that have been applied to the root node since the last call to [rewrite].
    pub fn get_applied_subs(&self) -> &[VarSubstitution] {
        &self.applied_subs
    }

    /// Perform a rewrite pass over the given node.
    /// This method applies the rules in the order they were added to the rewriter.
    /// It first applies the rules to the children of the node and then to the node itself.
    /// A single pass calls every rule once for every node in the AST.
    fn pass(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        // Apply equivalence rules
        let mut applied = false;
        let mut new_node = match self.pass_equivalence(node, &Vec::new(), mngr) {
            Some(rw) => {
                applied = true;
                rw
            }
            None => node.clone(),
        };

        // Apply entailment rules
        match self.pass_entailment(&new_node, mngr) {
            Some(rw) => {
                applied = true;
                new_node = rw;
            }
            None => {}
        }

        if applied {
            Some(new_node)
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

impl Default for Rewriter {
    fn default() -> Self {
        let mut equiv_rules: Vec<Box<dyn EquivalenceRule>> = Vec::new();

        equiv_rules.push(Box::new(boolean::OrAssocFlatten));
        equiv_rules.push(Box::new(boolean::AndAssocFlatten));
        equiv_rules.push(Box::new(boolean::AndConst));
        equiv_rules.push(Box::new(boolean::AndIdem));
        equiv_rules.push(Box::new(boolean::AndComp));
        equiv_rules.push(Box::new(boolean::OrConst));
        equiv_rules.push(Box::new(boolean::OrIdem));
        equiv_rules.push(Box::new(boolean::OrComp));
        equiv_rules.push(Box::new(boolean::NotConst));
        equiv_rules.push(Box::new(boolean::NotDoubleNegation));
        equiv_rules.push(Box::new(boolean::EqualityTrivial));

        equiv_rules.push(Box::new(regex::InReConstantLhs));
        equiv_rules.push(Box::new(regex::InReTrivial));
        equiv_rules.push(Box::new(regex::InReEquation));
        equiv_rules.push(Box::new(regex::InReStripPrefix));
        equiv_rules.push(Box::new(regex::InReStripSuffix));
        equiv_rules.push(Box::new(regex::InRePullComp));

        equiv_rules.push(Box::new(int::FoldConstantInts));
        equiv_rules.push(Box::new(int::LessTrivial));
        equiv_rules.push(Box::new(int::GreaterTrivial));
        equiv_rules.push(Box::new(int::EqualityTrivial));
        equiv_rules.push(Box::new(int::DistributeNeg));
        // does not seem to help
        equiv_rules.push(Box::new(int::NormalizeIneq));
        equiv_rules.push(Box::new(int::NotComparison));

        equiv_rules.push(Box::new(fwd::LinIntForward));

        equiv_rules.push(Box::new(strlen::StringLengthAddition));
        equiv_rules.push(Box::new(strlen::ConstStringLength));
        equiv_rules.push(Box::new(strlen::LengthTrivial));
        equiv_rules.push(Box::new(strlen::TrivialLenghtConstraints));

        // Hurts forward reasoning
        //equiv_rules.push(Box::new(strlen::LengthToReg));

        equiv_rules.push(Box::new(weq::ConstMismatch));
        equiv_rules.push(Box::new(weq::StripLCP));
        equiv_rules.push(Box::new(weq::StripLCS));
        equiv_rules.push(Box::new(weq::LengthReasoning));
        equiv_rules.push(Box::new(weq::ParikhMatrixMismatch));

        equiv_rules.push(Box::new(factors::TrivialPrefixof));
        equiv_rules.push(Box::new(factors::TrivialSuffixof));
        equiv_rules.push(Box::new(factors::TrivialContains));
        equiv_rules.push(Box::new(factors::FactorOfEmptyString));

        equiv_rules.push(Box::new(substr::SubstrConst));
        equiv_rules.push(Box::new(substr::SubstrNegative));
        equiv_rules.push(Box::new(substr::AtNegative));
        equiv_rules.push(Box::new(substr::AtConst));

        equiv_rules.push(Box::new(replace::ReplaceIdem));
        equiv_rules.push(Box::new(replace::ReplaceInEpsilon));
        equiv_rules.push(Box::new(replace::ReplaceSelf));
        equiv_rules.push(Box::new(replace::ReplaceEpsilon));

        equiv_rules.push(Box::new(str_int::ToIntConstant));
        equiv_rules.push(Box::new(str_int::FromIntConstant));
        equiv_rules.push(Box::new(str_int::VarEqConstantToInt));

        /* Entailment rules */
        let mut entail_rules: Vec<Box<dyn EntailmentRule>> = Vec::new();
        entail_rules.push(Box::new(regex::ConstantPrefixSuffix));
        entail_rules.push(Box::new(
            independent::IndependentVariableAssignment::default(),
        ));
        entail_rules.push(Box::new(strlen::ZeroLengthEpsilon));
        entail_rules.push(Box::new(levis::LevisRule));
        entail_rules.push(Box::new(entailed::EntailedBooleanVars));
        entail_rules.push(Box::new(entailed::EntailedAssigments));

        Rewriter {
            equiv_rules,
            entail_rules,
            rewrite_cache: IndexMap::new(),
            applied_subs: Vec::new(),
        }
    }
}
