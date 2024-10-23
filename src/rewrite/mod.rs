/// Rewrite rules for transforming Boolean nodes.
mod boolean;
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
    max_passes: usize,
}

impl Default for Rewriter {
    fn default() -> Self {
        Rewriter {
            rules: vec![
                Box::new(boolean::BoolConstFolding),
                Box::new(weq::WeqStripPrefix),
                Box::new(weq::WeqStripSuffix),
                Box::new(regex::ReStripConstant),
            ],
            rewrite_cache: IndexMap::new(),
            max_passes: 100,
        }
    }
}

impl Rewriter {
    /// Rewrite the given node using the rules in this rewriter.
    /// Performs up to `max_passes` passes over the node.
    /// Each pass traverses the AST in post-order, applying the rules.
    pub fn rewrite(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        self.rewrite_cache.clear();
        let mut current = None;
        for _ in 0..self.max_passes {
            current = self.rewrite_pass(node, mngr);
            if current.is_none() {
                break;
            }
        }
        current
    }

    /// Does a post-order traversal of the AST, applying the matching rule.
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
        let new_node = mngr.create_node(node.kind().clone(), children);
        for rule in &self.rules {
            if let Some(result) = rule.apply(&new_node, mngr) {
                return Some(result);
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
}
