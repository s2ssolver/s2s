use std::{
    //cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    rc::Rc,
};

use regulaer::{automaton::NFA, compiler::Compiler, re::Regex};

use crate::repr::{ast::AstBuilder, ir::IrBuilder, Sort, Sorted, Variable};

#[derive(Default)]
pub struct Context {
    /// Manages the variables
    variables: HashMap<String, Rc<Variable>>,
    temp_vars: HashSet<Rc<Variable>>,

    //ast_builder: RefCell<AstBuilder>,
    ast_builder: AstBuilder,
    //ir_builder: RefCell<IrBuilder>,
    ir_builder: IrBuilder,

    nfa_cache: HashMap<Regex, Rc<NFA>>,
}

impl Context {
    /// Creates a new variable.
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

    /// Returns an iterator over all variables of the given sort.
    /// Includes temporary variables.
    pub fn vars_with_sort(&self, sort: Sort) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.variables
            .values()
            .filter(move |v| v.sort() == sort)
            .chain(self.temp_vars.iter().filter(move |v| v.sort() == sort))
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
    pub fn ast_builder(&mut self) -> &mut AstBuilder {
        &mut self.ast_builder
    }

    // pub fn ast_builder(&self) -> RefMut<AstBuilder> {
    //     self.ast_builder.borrow_mut()
    // }

    // /// Returns the instance of the [IrBuilder] that is shared by this context.
    // /// The [IrBuilder] is used to create IR nodes.
    pub fn ir_builder(&mut self) -> &mut IrBuilder {
        &mut self.ir_builder
    }

    /// Returns the NFA for the given regular expression.
    /// Computes the NFA if it has not been computed yet.
    pub fn get_nfa(&mut self, regex: &Regex) -> Rc<NFA> {
        if let Some(nfa) = self.nfa_cache.get(regex) {
            nfa.clone()
        } else {
            let builder = self.ast_builder().re_builder();
            let nfa = Compiler::Thompson
                .nfa(regex, builder)
                .map(|nfa| nfa.remove_epsilons().expect("Failed to compile regex"))
                .expect("Failed to compile regex");

            let nfa = Rc::new(nfa);
            self.nfa_cache.insert(regex.clone(), nfa.clone());
            nfa
        }
    }

    // pub fn ir_builder(&self) -> RefMut<IrBuilder> {
    //     self.ir_builder.borrow_mut()
    // }
}
