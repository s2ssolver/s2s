use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    rc::Rc,
};

use super::{canonical::Assignment, Node, NodeKind, NodeManager, Variable};

/// A substitution that maps nodes to other nodes.
///
/// The `NodeSubstitution` structure represents a mapping from one node to another. This allows transforming or substituting certain nodes with new nodes according to the mapping provided.
///
/// The substitution is guarantueed to be consistent. This means that the substitution is an homomorphism:
/// Applying the substitution to node `n` is equivalent to applying the substitution to all children of `n` and then creating a new node with the same kind as `n` and the substituted children.
/// This is ensured by the `add` function, which essentially only allows composing the substitution with other substitutions that are also consistent.
/// Substitutions might be ciclic, but they are always guaranteed to terminate.
#[derive(Debug, Clone, Default)]
pub struct VarSubstitution {
    map: HashMap<Rc<Variable>, Node>,
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

    // Returns the composition of this substitution with another substitution.
    /// This has the same effect as applying this substitution first, and then applying the other substitution to the result.
    /// Applies the other substitution to all values in this substitution.
    pub fn compose(&self, other: VarSubstitution, mngr: &mut NodeManager) -> Self {
        let mut subst = VarSubstitution::default();

        // Apply the other substitution to all values in this substitution.
        for (key, value) in self.iter() {
            let new_value = other.apply(value, mngr);
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

    /// Apply the substitution to the given node.
    pub fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Node {
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
            .map(|child| self.apply(child, mngr))
            .collect();

        mngr.create_node(node.kind().clone(), children)
    }

    pub fn from_assignment(assignment: &Assignment, mngr: &mut NodeManager) -> Self {
        let mut subst = VarSubstitution::default();
        for (var, value) in assignment.iter() {
            let value = if let Some(true) = value.as_bool() {
                mngr.ttrue()
            } else if let Some(false) = value.as_bool() {
                mngr.ffalse()
            } else if let Some(str) = value.as_string() {
                mngr.const_string(str.clone())
            } else if let Some(int) = value.as_int() {
                mngr.const_int(int)
            } else {
                panic!("Unsupported value in assignment")
            };
            subst.add(var.clone(), value);
        }
        subst
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
            writeln!(f, "{} -> {}", key, value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::node::Sort;

    use super::*;

    #[test]
    fn add_var_to_var() {
        let mut mngr = NodeManager::default();
        let mut subst = VarSubstitution::default();

        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        subst.add(a.clone(), bnode.clone());

        assert_eq!(subst.apply(&anode, &mut mngr), bnode);
        assert_eq!(subst.apply(&bnode, &mut mngr), bnode);
    }

    #[test]
    fn compose_var_to_var() {
        let mut mngr = NodeManager::default();

        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let c = mngr.temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());

        let mut subst1 = VarSubstitution::default();
        subst1.add(a.clone(), bnode.clone()); // a -> b

        let mut subst2 = VarSubstitution::default();
        subst2.add(b.clone(), cnode.clone()); // b -> c

        let comp = subst1.compose(subst2, &mut mngr);

        assert_eq!(comp.apply(&anode, &mut mngr), cnode);
        assert_eq!(comp.apply(&bnode, &mut mngr), cnode);
    }

    #[test]
    fn compose_var_to_var_2() {
        let mut mngr = NodeManager::default();

        let a = mngr.temp_var(Sort::Bool);
        let b = mngr.temp_var(Sort::Bool);
        let c = mngr.temp_var(Sort::Bool);

        let anode = mngr.var(a.clone());
        let bnode = mngr.var(b.clone());
        let cnode = mngr.var(c.clone());

        let mut subst1 = VarSubstitution::default();
        subst1.add(a.clone(), bnode.clone()); // a -> b

        let mut subst2 = VarSubstitution::default();
        subst2.add(b.clone(), cnode.clone()); // b -> c

        let comp = subst2.compose(subst1, &mut mngr);

        assert_eq!(comp.apply(&anode, &mut mngr), bnode);
        assert_eq!(comp.apply(&bnode, &mut mngr), cnode);
    }
}
