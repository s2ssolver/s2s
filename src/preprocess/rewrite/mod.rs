/// Rewrite rules for transforming Boolean nodes.
mod boolean;
mod int;
mod ite;
mod regex;
mod weq;

use indexmap::IndexMap;

use crate::node::{Node, NodeManager};

pub trait RewriteRule {
    /// Apply the rule to a node, returning the new node if the rule applies and None otherwise.
    /// This method may lookup children of the given node but should never recurse.
    fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node>;
}

pub struct Rewriter {
    rules: Vec<Box<dyn RewriteRule>>,
    rewrite_cache: IndexMap<Node, Node>,
    // The applied rules are stored as pairs of (original, rewritten) nodes.
    // This is used for debugging and logging purposes.
    // Only contains the rewrite on the level where the rule was applied.
    // If that lead to parent nodes being affected, they are not included (as they are in rewrite_cache).
    applied_rules: Vec<(Node, Node)>,
}

impl Default for Rewriter {
    fn default() -> Self {
        Rewriter {
            rules: vec![
                Box::new(ite::IteRewrite),
                Box::new(boolean::BoolConstFolding),
                Box::new(weq::FoldTrivialEquations),
                Box::new(weq::WeqStripPrefix),
                Box::new(weq::WeqStripSuffix),
                Box::new(weq::WeqConstMismatch),
                Box::new(regex::FoldConstantInRe),
                Box::new(regex::FoldConstantRegex),
                Box::new(regex::ReStripConstantPrefix),
                Box::new(regex::ReStripConstantSuffix),
                Box::new(regex::PullComplement),
                Box::new(int::LengthOfConcatToAddition),
                Box::new(int::TrivialIntRelations),
                Box::new(int::FoldConstantInts),
            ],
            rewrite_cache: IndexMap::new(),
            applied_rules: Vec::new(),
        }
    }
}

impl Rewriter {
    /// Rewrite the given node using the rules in this rewriter.
    /// Performs up to `max_passes` passes over the node.
    /// Each pass traverses the AST in post-order, applying the rules.
    pub fn rewrite(&mut self, node: &Node, passes: usize, mngr: &mut NodeManager) -> Option<Node> {
        self.rewrite_cache.clear();
        self.applied_rules.clear();

        let node = pull_ites(node, mngr);
        let mut current = None;
        for _ in 0..passes {
            match self.rewrite_pass(current.as_ref().unwrap_or(&node), mngr) {
                Some(rew) => current = Some(rew),
                None => break,
            }
        }

        current
    }

    /// Does a post-order traversal of the AST, applying the matching rules.
    /// If a rule matches, then the node is replaced with the result of the rule.
    /// If no rule matches, then the node is unchanged.
    /// This method returns None if no rule was applied.
    fn rewrite_pass(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        // Check was already rewritten.
        // If so, return the cached result.
        if let Some(new_node) = self.rewrite_cache.get(node) {
            return Some(new_node.clone());
        }

        let mut children = Vec::new();
        let mut applied = false;
        for child in node.children() {
            if let Some(new_child) = self.rewrite_pass(child, mngr) {
                children.push(new_child);
                applied = true;
            } else {
                children.push(child.clone());
            }
        }
        let mut new_node = mngr.create_node(node.kind().clone(), children);
        for rule in &self.rules {
            if let Some(result) = rule.apply(&new_node, mngr) {
                self.applied_rules.push((new_node.clone(), result.clone()));
                applied = true;
                new_node = result;
                break;
            }
        }
        if applied {
            self.rewrite_cache
                .insert(new_node.clone(), new_node.clone());
            Some(new_node)
        } else {
            None
        }
    }

    /// Returns the applied rules.
    pub fn applied(&self) -> &[(Node, Node)] {
        &self.applied_rules
    }
}

/// Pulls all ITE expressions that return non-boolean values to a Boolean level.
/// Meaning, if node contains a non-Boolean predicate P (..., ITE c t e, ...), then this will ''pull'' the ITE expression one level higher: ITE c (P ..., t, ...) (P ..., e, ...)
pub fn pull_ites(node: &Node, mngr: &mut NodeManager) -> Node {
    let ch_normed = node.children().iter().map(|c| pull_ites(c, mngr)).collect();
    let new_node = mngr.create_node(node.kind().clone(), ch_normed);
    if let Some(rew) = ite::PullIte.apply(&new_node, mngr) {
        rew
    } else {
        new_node
    }
}
