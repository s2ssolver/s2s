use std::{
    fmt::{Display, Formatter},
    rc::Rc,
};

use indexmap::IndexMap;

use crate::context::{Context, Variable};

use super::{Node, NodeKind};

/// A substitution that maps nodes to other nodes.
///
/// The `NodeSubstitution` structure represents a mapping from one node to another. This allows transforming or substituting certain nodes with new nodes according to the mapping provided.
///
/// The substitution is guarantueed to be consistent. This means that the substitution is an homomorphism:
/// Applying the substitution to node `n` is equivalent to applying the substitution to all children of `n` and then creating a new node with the same kind as `n` and the substituted children.
/// This is ensured by the `add` function, which essentially only allows composing the substitution with other substitutions that are also consistent.
/// Substitutions might be ciclic, but they are always guaranteed to terminate.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VarSubstitution {
    map: IndexMap<Rc<Variable>, Node>,
}

impl VarSubstitution {
    /// Insert a key-value pair into the substitution map.
    /// This function might break the consistency condition of the substitution.
    /// It thus not intended to be used directly, but only used internallay
    fn insert(&mut self, key: Rc<Variable>, value: Node) {
        // Insert the key-value pair into the substitution map.
        self.map.insert(key, value);
    }

    /// Add a new key-value pair to the substitution map.
    /// Panics if the key is already in the substitution map.
    /// Adviced to use `compose` instead
    pub fn add(&mut self, key: Rc<Variable>, value: Node) {
        if self.map.contains_key(&key) {
            panic!("Variable already in substitution");
        }
        self.insert(key, value);
    }

    /// Adds all key-value pairs in other to this substitution.
    /// Panics if a key exists in both.
    pub fn extend(&mut self, other: &Self) {
        for (k, v) in other.iter() {
            self.add(k.clone(), v.clone());
        }
    }

    /// Get the value for the given key.
    /// Returns `None` if the key is not in the substitution map.
    pub fn get(&self, key: &Rc<Variable>) -> Option<&Node> {
        self.map.get(key)
    }

    // Returns the composition of this substitution with another substitution.
    /// This has the same effect as applying this substitution first, and then applying the other substitution to the result.
    /// Applies the other substitution to all values in this substitution.
    pub fn compose(&self, other: VarSubstitution, ctx: &mut Context) -> Self {
        let mut subst = VarSubstitution::default();

        // Apply the other substitution to all values in this substitution.
        for (key, value) in self.iter() {
            let new_value = other.apply(value, ctx);
            subst.add(key.clone(), new_value);
        }
        // ensure that all keys in the other substitution are in the new substitution
        for (key, value) in other.iter() {
            if !subst.map.contains_key(key) {
                subst.add(key.clone(), value.clone());
            }
        }

        subst
    }

    /// Check if the substitution is the identity substitution.
    /// The identity substitution maps every variable to itself.
    pub fn is_identity(&self) -> bool {
        self.map.iter().all(|(k, v)| {
            if let NodeKind::Variable(v2) = v.kind() {
                k == v2
            } else {
                false
            }
        })
    }

    /// Check if the substitution is empty.
    /// An empty substitution does not map any variable to a value.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Apply the substitution to the given node.
    pub fn apply(&self, node: &Node, ctx: &mut Context) -> Node {
        // If the node is in the substitution map, return the corresponding value.
        // Because the substitution is an automorphism, recursion will terminate once the substitution is applied to a node.
        if let NodeKind::Variable(v) = node.kind() {
            if let Some(value) = self.map.get(v) {
                return value.clone();
            } else {
                return node.clone();
            }
        }

        // Otherwise, recursively apply the substitution to the children of the node.
        let children = node
            .children()
            .iter()
            .map(|child| self.apply(child, ctx))
            .collect();

        ctx.ast().create_node(node.kind().clone(), children)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<Variable>, &Node)> {
        self.map.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Rc<Variable>, &mut Node)> {
        self.map.iter_mut()
    }
}

impl Display for VarSubstitution {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (key, value) in self.map.iter() {
            write!(f, "{} -> {}; ", key, value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::context::Sort;

    use super::*;

    #[test]
    fn add_var_to_var() {
        let mut ctx = Context::default();
        let mut subst = VarSubstitution::default();

        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);

        let anode = ctx.ast().variable(a.clone());
        let bnode = ctx.ast().variable(b.clone());
        subst.add(a.clone(), bnode.clone());

        assert_eq!(subst.apply(&anode, &mut ctx), bnode);
        assert_eq!(subst.apply(&bnode, &mut ctx), bnode);
    }

    #[test]
    fn compose_var_to_var() {
        let mut ctx = Context::default();

        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let c = ctx.temp_var(Sort::Bool);

        let anode = ctx.ast().variable(a.clone());
        let bnode = ctx.ast().variable(b.clone());
        let cnode = ctx.ast().variable(c.clone());

        let mut subst1 = VarSubstitution::default();
        subst1.add(a.clone(), bnode.clone()); // a -> b

        let mut subst2 = VarSubstitution::default();
        subst2.add(b.clone(), cnode.clone()); // b -> c

        let comp = subst1.compose(subst2, &mut ctx);

        assert_eq!(comp.apply(&anode, &mut ctx), cnode);
        assert_eq!(comp.apply(&bnode, &mut ctx), cnode);
    }

    #[test]
    fn compose_var_to_var_2() {
        let mut ctx = Context::default();

        let a = ctx.temp_var(Sort::Bool);
        let b = ctx.temp_var(Sort::Bool);
        let c = ctx.temp_var(Sort::Bool);

        let anode = ctx.ast().variable(a.clone());
        let bnode = ctx.ast().variable(b.clone());
        let cnode = ctx.ast().variable(c.clone());

        let mut subst1 = VarSubstitution::default();
        subst1.add(a.clone(), bnode.clone()); // a -> b

        let mut subst2 = VarSubstitution::default();
        subst2.add(b.clone(), cnode.clone()); // b -> c

        let comp = subst2.compose(subst1, &mut ctx);

        assert_eq!(comp.apply(&anode, &mut ctx), bnode);
        assert_eq!(comp.apply(&bnode, &mut ctx), cnode);
    }
}
