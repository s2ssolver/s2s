use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
};

use super::{Node, NodeManager};

/// A substitution that maps nodes to other nodes.
///
/// The `NodeSubstitution` structure represents a mapping from one node to another. This allows transforming or substituting certain nodes with new nodes according to the mapping provided.
///
/// The substitution is guarantueed to be consistent. This means that the substitution is an homomorphism:
/// Applying the substitution to node `n` is equivalent to applying the substitution to all children of `n` and then creating a new node with the same kind as `n` and the substituted children.
/// This is ensured by the `add` function, which essentially only allows composing the substitution with other substitutions that are also consistent.
/// Substitutions might be ciclic, but they are always guaranteed to terminate.
#[derive(Debug, Clone, Default)]
pub struct NodeSubstitution {
    map: HashMap<Node, Node>,
}

impl NodeSubstitution {
    /// Insert a key-value pair into the substitution map.
    /// This function might break the consistency condition of the substitution.
    /// It thus not intended to be used directly, but only used internallay
    fn insert(&mut self, key: Node, value: Node) {
        // Insert the key-value pair into the substitution map.
        self.map.insert(key, value);
    }

    /// Add a new key-value pair to the substitution map.
    /// This takes O(n) time, where n is the number of key-value pairs in the substitution map.
    pub fn add(&mut self, key: Node, value: Node, mngr: &mut NodeManager) {
        let mut as_sub = NodeSubstitution::default();
        as_sub.insert(key.clone(), value.clone());

        let mut new_map = HashMap::with_capacity(self.map.len() + 1);
        // Apply the substitution to all key-value pairs in the substitution map.
        for (k, v) in self.map.iter() {
            let composed_v = as_sub.apply(v, mngr);
            let composed_k = as_sub.apply(k, mngr);
            new_map.insert(composed_k.clone(), composed_v);
        }
        // Insert the new key-value pair into the substitution map.
        new_map.insert(key, value);

        // Update the substitution map.
        self.map = new_map;
    }

    /// Compose this substitution with another substitution.
    /// Essentially, this function applies the other substitution to all values in this substitution.
    pub fn compose(mut self, other: Self, mngr: &mut NodeManager) -> Self {
        for (key, value) in other.map {
            self.add(key, value, mngr);
        }
        self
    }

    /// Apply the substitution to the given node.
    pub fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Node {
        // If the node is in the substitution map, return the corresponding value.
        // Because the substitution is an automorphism, recursion will terminate once the substitution is applied to a node.
        if let Some(value) = self.map.get(node) {
            return value.clone();
        }

        // Otherwise, recursively apply the substitution to the children of the node.
        let children = node
            .children()
            .iter()
            .map(|child| self.apply(child, mngr))
            .collect();

        let node = mngr.create_node(node.kind().clone(), children);

        // check if the node is in the substitution map
        // if it is, return the corresponding value
        if let Some(value) = self.map.get(&node) {
            value.clone()
        } else {
            node
        }
    }
}

impl Display for NodeSubstitution {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (key, value) in self.map.iter() {
            writeln!(f, "{} -> {}", key, value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::context::{Context, Sort};

    use super::*;

    #[test]
    fn add_var_to_var() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        subst.add(anode.clone(), bnode.clone(), &mut mngr);

        assert_eq!(subst.apply(&anode, &mut mngr), bnode);
        assert_eq!(subst.apply(&bnode, &mut mngr), bnode);
    }

    #[test]
    fn add_var_to_var_transitive() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);
        let c = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());

        subst.add(anode.clone(), bnode.clone(), &mut mngr);
        subst.add(bnode.clone(), cnode.clone(), &mut mngr);

        assert_eq!(subst.apply(&anode, &mut mngr), cnode);
        assert_eq!(subst.apply(&bnode, &mut mngr), cnode);
    }

    #[test]
    #[should_panic]
    fn add_var_refl() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        subst.add(anode.clone(), anode.clone(), &mut mngr);
    }

    #[test]
    #[should_panic]
    fn add_var_refl_transitive() {
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);
        let c = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());
        subst.add(anode.clone(), bnode.clone(), &mut mngr);
        subst.add(bnode.clone(), cnode.clone(), &mut mngr);
        subst.add(cnode.clone(), anode.clone(), &mut mngr);
    }

    #[test]
    fn add_and_to_var() {
        // a&b -> c
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);
        let c = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());
        let a_and_b = mngr.and(vec![anode.clone(), bnode.clone()]);
        subst.add(a_and_b.clone(), cnode.clone(), &mut mngr);
        assert_eq!(subst.apply(&a_and_b, &mut mngr), cnode);
    }

    #[test]
    fn add_and_to_var_semicyclic() {
        // a && b -> c, c -> a => a && b -> a
        // This is not invalid because there is no substitution for a
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);
        let c = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());
        let a_and_b = mngr.and(vec![anode.clone(), bnode.clone()]);
        subst.add(a_and_b.clone(), cnode.clone(), &mut mngr);
        subst.add(cnode.clone(), anode.clone(), &mut mngr);

        assert_eq!(subst.apply(&a_and_b, &mut mngr), anode);
    }

    #[test]
    fn add_and_to_var_transitive_key() {
        // a && b -> c, a -> b => b && b -> c
        let mut ctx = Context::default();
        let mut mngr = NodeManager::default();
        let mut subst = NodeSubstitution::default();

        let a = ctx.new_temp_var(Sort::Bool);
        let b = ctx.new_temp_var(Sort::Bool);
        let c = ctx.new_temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());
        let a_and_b = mngr.and(vec![anode.clone(), bnode.clone()]);
        subst.add(a_and_b.clone(), cnode.clone(), &mut mngr);
        subst.add(anode.clone(), bnode.clone(), &mut mngr);

        let b_and_b = mngr.and(vec![bnode.clone(), bnode.clone()]);
        assert_eq!(subst.apply(&a_and_b, &mut mngr), cnode);
        assert_eq!(subst.apply(&b_and_b, &mut mngr), cnode);
    }
}
