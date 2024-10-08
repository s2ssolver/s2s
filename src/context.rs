use std::hash::{Hash, Hasher};
use std::{
    //cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    fmt::Display,
    rc::Rc,
    time::Instant,
};

use regulaer::re::ReBuilder;
use regulaer::{
    automaton::NFA,
    compiler::{Compiler, Thompson},
    re::Regex,
};

use crate::ir::IrBuilder;

pub type Id = usize;

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
    id: Id,
    name: String,
    sort: Sort,
}
impl Variable {
    pub(crate) fn new(id: Id, name: String, sort: Sort) -> Self {
        assert!(!name.chars().any(|c| c == '|'));
        Self { id, name, sort }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the unique identifier of the variable.
    #[allow(dead_code)]
    pub(crate) fn id(&self) -> Id {
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
        if self.name.chars().all(|c| c.is_ascii_alphabetic()) {
            write!(f, "{}", self.name)
        } else {
            write!(f, "|{}|", self.name)
        }
    }
}
impl Sorted for Variable {
    fn sort(&self) -> Sort {
        self.sort
    }
}

#[derive(Default)]
pub struct Context {
    /// Manages the variables
    variables: HashMap<String, Rc<Variable>>,
    /// Subset of variables that are temporary and should be removed after use.
    temp_vars: HashSet<Rc<Variable>>,

    //ast_builder: RefCell<AstBuilder>,

    //ir_builder: RefCell<IrBuilder>,
    ir_builder: IrBuilder,
    re_builder: ReBuilder,

    nfa_cache: HashMap<Regex, Rc<NFA>>,
}

impl Context {
    /// Creates a new variable.
    /// If no variable with the same name exists, a new variable is created and returned.
    /// If a variable with the same name and same sort already exists, it is returned.
    /// If a variable with the same name but different sort already exists, None is returned.
    pub fn make_var(&mut self, name: String, sort: Sort) -> Option<Rc<Variable>> {
        if let Some(v) = self.variables.get(&name) {
            if v.sort() == sort {
                Some(v.clone())
            } else {
                None
            }
        } else {
            let id = self.variables.len();
            let v = Rc::new(Variable::new(id, name.clone(), sort));
            self.variables.insert(name, v.clone());
            Some(v)
        }
    }

    pub fn new_temp_var(&mut self, sort: Sort) -> Rc<Variable> {
        let name = format!("__temp_{}", self.variables.len());
        let v = self.make_var(name.clone(), sort).unwrap();
        self.temp_vars.insert(v.clone());
        v
    }

    /// Returns the variable with the given name.
    pub fn get_var(&self, name: &str) -> Option<Rc<Variable>> {
        self.variables.get(name).cloned()
    }

    /// Returns true if the given variable is temporary.
    pub fn is_temp_var(&self, var: &Variable) -> bool {
        self.temp_vars.contains(var)
    }

    /// Returns an iterator over all variables of the given sort.
    /// Includes temporary variables.
    pub fn vars_with_sort(&self, sort: Sort) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.variables.values().filter(move |v| v.sort() == sort)
    }

    pub fn vars(&self) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.variables.values().chain(self.temp_vars.iter())
    }

    /// Returns an iterator over all integer variables.
    /// Includes temporary variables.
    pub fn string_vars(&self) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.vars_with_sort(Sort::String)
    }

    /// Returns an iterator over all integer variables.
    /// Includes temporary variables.
    pub fn int_vars(&self) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.vars_with_sort(Sort::Int)
    }

    // /// Returns the instance of the [AstBuilder] that is shared by this context.
    // /// The [AstBuilder] is used to create AST nodes.
    // /// The builder also allows access to the [ReBuilder] that is used to create regular expressions.
    // /// Regular expressions built using the [ReBuilder] are used in both the AST as well as in the IR.
    // pub fn ast_builder(&mut self) -> &mut AstBuilder {
    //     &mut self.ast_builder
    // }

    // pub fn ast_builder(&self) -> RefMut<AstBuilder> {
    //     self.ast_builder.borrow_mut()
    // }

    /// Returns the instance of the [IrBuilder] that is shared by this context.
    /// The [IrBuilder] is used to create IR nodes.
    pub fn ir_builder(&mut self) -> &mut IrBuilder {
        &mut self.ir_builder
    }

    /// Returns the instance of the [ReBuilder] that is shared by this context.
    /// The [ReBuilder] is used to create regular expressions.
    pub fn re_builder(&mut self) -> &mut ReBuilder {
        &mut self.re_builder
    }

    /// Returns the NFA for the given regular expression.
    /// Computes the NFA if it has not been computed yet.
    pub fn get_nfa(&mut self, regex: &Regex) -> Rc<NFA> {
        let t = Instant::now();
        let nfa = if let Some(nfa) = self.nfa_cache.get(regex) {
            nfa.clone()
        } else {
            let builder = self.re_builder();

            let nfa = Thompson::default()
                .compile(regex, builder)
                .map(|nfa| nfa.remove_epsilons().expect("Failed to compile regex"))
                .expect("Failed to compile regex");

            let nfa = Rc::new(nfa);
            self.nfa_cache.insert(regex.clone(), nfa.clone());
            nfa
        };
        log::debug!("Compiled NFA ({:?})", t.elapsed());
        nfa
    }

    // pub fn ir_builder(&self) -> RefMut<IrBuilder> {
    //     self.ir_builder.borrow_mut()
    // }
}
