use indexmap::{IndexMap, IndexSet};

use crate::node::Node;

/// Partitions the nodes into classes based on variable dependencies.
/// Two ndoes are in the same class if
/// - they share a variable, or
/// - they is a chain of nodes that share variables between them.
/// In other words, each class is the reflexive transitive closure of the relation "share a variable".
pub fn partition_by_vars(nodes: &[Node]) -> Vec<Vec<Node>> {
    // Build a graph where each literal is a vertex and there is an edge between two literals if they share a variable

    let mut lit2vars = IndexMap::new();
    let mut var2lits = IndexMap::new();
    for node in nodes {
        let vars = node.variables();
        for v in &vars {
            var2lits
                .entry(v.clone())
                .or_insert_with(Vec::new)
                .push(node);
        }
        lit2vars.insert(node, vars);
    }

    let mut edges = IndexMap::new();
    for node in nodes {
        for var in node.variables() {
            // Find all literals that share this variable
            for &dep_lit in var2lits.get(&var).unwrap() {
                if dep_lit != node {
                    // Add an edge between the literals
                    edges.entry(node).or_insert_with(Vec::new).push(dep_lit);
                    edges.entry(dep_lit).or_insert_with(Vec::new).push(node);
                }
            }
        }
    }

    // Find the connected components of the graph using DFS until all vertices are visited
    let mut unvisited = nodes.iter().collect::<IndexSet<_>>();
    let mut components = Vec::new();
    while let Some(&lit) = unvisited.iter().next() {
        let mut stack = vec![lit];
        let mut component = Vec::new();
        while let Some(lit) = stack.pop() {
            if unvisited.remove(lit) {
                component.push(lit.clone());
                for &dep_lit in edges.get(lit).unwrap_or(&Vec::new()) {
                    stack.push(dep_lit);
                }
            }
        }
        components.push(component);
    }
    // Return the literals in each connected component
    components
}
