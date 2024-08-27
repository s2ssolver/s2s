use std::collections::{HashMap, HashSet};

use super::Literal;

/// Partitions the literals into classes based on variable dependencies.
/// Two literals are in the same class if
/// - they share a variable, or
/// - they is a chain of literals that share variables between them.
/// In other words, each class is the reflexive transitive closure of the relation "share a variable".
pub fn partition_by_vars(lits: &[Literal]) -> Vec<Vec<Literal>> {
    // Build a graph where each literal is a vertex and there is an edge between two literals if they share a variable

    let mut lit2vars = HashMap::new();
    let mut var2lits = HashMap::new();
    for lit in lits {
        let vars = lit.variables();
        for v in &vars {
            var2lits.entry(v.clone()).or_insert_with(Vec::new).push(lit);
        }
        lit2vars.insert(lit, vars);
    }

    let mut edges = HashMap::new();
    for lit in lits {
        for var in lit.variables() {
            // Find all literals that share this variable
            for &dep_lit in var2lits.get(&var).unwrap() {
                if dep_lit != lit {
                    // Add an edge between the literals
                    edges.entry(lit).or_insert_with(Vec::new).push(dep_lit);
                    edges.entry(dep_lit).or_insert_with(Vec::new).push(lit);
                }
            }
        }
    }

    // Find the connected components of the graph using DFS until all vertices are visited
    let mut unvisited = lits.iter().collect::<HashSet<_>>();
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
