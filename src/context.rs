use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    rc::Rc,
    time::Instant,
};

use indexmap::IndexMap;

use smt_str::{
    automata::{compile, NFA},
    re::Regex,
};

use crate::{
    ast::{AstBuilder, Node},
    ir::{self, Literal},
};

/// The SMT-LIB sorts.
/// Currently, only Int, String, and Bool are supported.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum Sort {
    Int,
    String,
    RegLan,
    Bool,
}
impl Sort {
    /// Returns true if the sort is Bool.
    pub fn is_bool(&self) -> bool {
        matches!(self, Sort::Bool)
    }

    /// Returns true if the sort is Int.
    pub fn is_int(&self) -> bool {
        matches!(self, Sort::Int)
    }

    /// Returns true if the sort is String.
    pub fn is_string(&self) -> bool {
        matches!(self, Sort::String)
    }

    /// Returns true if the sort is RegLang.
    pub fn is_reglang(&self) -> bool {
        matches!(self, Sort::RegLan)
    }
}
impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Int => write!(f, "Int"),
            Sort::String => write!(f, "String"),
            Sort::RegLan => write!(f, "RegLang"),
            Sort::Bool => write!(f, "Bool"),
        }
    }
}
pub trait Sorted {
    fn sort(&self) -> Sort;
}

/// A variable.
/// Variables are uniquely identified by their name.
/// Every variable has a sort.
#[derive(Debug, Clone)]
pub struct Variable {
    id: usize,
    name: String,
    sort: Sort,
}
impl Variable {
    pub(crate) fn new(id: usize, name: String, sort: Sort) -> Self {
        assert!(!name.chars().any(|c| c == '|'));
        Self { id, name, sort }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the unique identifier of the variable.
    #[allow(dead_code)]
    pub(crate) fn id(&self) -> usize {
        self.id
    }
}
impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Variable {}
impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.name)
    }
}
impl Sorted for Variable {
    fn sort(&self) -> Sort {
        self.sort
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ContextError {
    #[error("Variable {0} of sort {1} already declared with sort {2}")]
    AlreadyDeclared(String, Sort, Sort),
}

#[derive(Default)]
pub struct Context {
    /// The next id to assign to variable
    next_id: usize,
    /// Regular expression builder
    re_builder: smt_str::re::ReBuilder,
    /// Registry of variables, indexed by name
    variables: IndexMap<String, Rc<Variable>>,
    /// Cached NFAs
    nfas: IndexMap<Regex, Rc<NFA>>,
    /// The instance of the AST builder valid for this context
    ast_builder: AstBuilder,

    /// Caches conversions from nodes to literals
    ir_cache: IndexMap<Node, Option<Literal>>,
}

impl Context {
    /* Variables */
    /// Creates a new variable with a given name and sort.
    /// If that variable already exists, returns the existing variable.
    /// If a variable with the same name but different sort exists, returns an error.
    pub fn new_var(&mut self, name: String, sort: Sort) -> Result<Rc<Variable>, ContextError> {
        if let Some(var) = self.variables.get(&name) {
            if var.sort() != sort {
                return Err(ContextError::AlreadyDeclared(name, sort, var.sort()));
            }
            Ok(var.clone())
        } else {
            let var = Rc::new(Variable::new(self.next_id, name.clone(), sort));
            self.next_id += 1;
            self.variables.insert(name.clone(), var.clone());
            Ok(var)
        }
    }

    /// Creates a new variable with a given name and Bool sort.
    /// If that variable already exists, returns the existing variable.
    /// If a variable with the same name but different sort exists, returns an error.
    pub fn bool_var(&mut self, name: &str) -> Result<Rc<Variable>, ContextError> {
        self.new_var(name.to_string(), Sort::Bool)
    }

    /// Creates a new variable with a given name and Int sort.
    /// If that variable already exists, returns the existing variable.
    /// If a variable with the same name but different sort exists, returns an error.
    pub fn int_var(&mut self, name: &str) -> Result<Rc<Variable>, ContextError> {
        self.new_var(name.to_string(), Sort::Int)
    }

    /// Creates a new variable with a given name and String sort.
    /// If that variable already exists, returns the existing variable.
    /// If a variable with the same name but different sort exists, panics.
    pub fn string_var(&mut self, name: &str) -> Result<Rc<Variable>, ContextError> {
        self.new_var(name.to_string(), Sort::String)
    }

    pub fn get_var(&self, name: &str) -> Option<Rc<Variable>> {
        self.variables.get(name).cloned()
    }

    /// Creates a new temporary variable with a given sort.
    pub fn temp_var(&mut self, sort: Sort) -> Rc<Variable> {
        let name = format!("__temp_{}", self.next_id);
        self.next_id += 1;
        self.new_var(name, sort).unwrap() // safe to unwrap
    }

    /// Returns an iterator over all variables in this context
    pub fn vars(&self) -> impl Iterator<Item = &Rc<Variable>> {
        self.variables.values()
    }

    /* Regex and NFA */

    /// Returns the builder for regular expressions.
    pub fn re_builder(&mut self) -> &mut smt_str::re::ReBuilder {
        &mut self.re_builder
    }

    /// Returns the NFA for the given regular expression.
    /// Computes the NFA if it has not been computed yet.
    pub fn get_nfa(&mut self, regex: &Regex) -> Rc<NFA> {
        let t = Instant::now();
        let nfa = if let Some(nfa) = self.nfas.get(regex) {
            nfa.clone()
        } else {
            let builder = self.re_builder();
            let mut nfa = compile(regex, builder).eliminate_epsilon();

            // Should be trim by construction, but just in case.
            // If the regex is trim, then this is a no-op anyway (returns the automaton directly).
            nfa = nfa.trim();
            // May help with performance, but not strictly necessary.
            nfa.compress_ranges();
            let nfa = Rc::new(nfa);
            self.nfas.insert(regex.clone(), nfa.clone());
            nfa
        };
        log::debug!(
            "Compiled NFA ({:?}) ({} states)",
            t.elapsed(),
            nfa.num_states()
        );

        nfa
    }

    /// Returns the [AstBuilder] valid for this context
    pub fn ast(&mut self) -> &mut AstBuilder {
        &mut self.ast_builder
    }

    /// Converts a node to a literal in IR.
    /// Caches the results
    pub fn to_ir(&mut self, node: &Node) -> Option<Literal> {
        if let Some(ok) = self.ir_cache.get(node) {
            ok.clone()
        } else {
            let converted = ir::convert_to_ir(node);
            self.ir_cache.insert(node.clone(), converted.clone());
            converted
        }
    }
}
