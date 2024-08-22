use std::{
    //cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    rc::Rc,
};

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
}

impl Context {
    /// Creates a new variable.
    /// If a variable with the same name and same sort already exists, it is returned.
    /// If a variable with the same name but different sort already exists, None is returned.
    pub fn new_var(&mut self, name: String, sort: Sort) -> Option<Rc<Variable>> {
        if let Some(v) = self.variables.get(&name) {
            if v.sort() == sort {
                Some(v.clone())
            } else {
                None
            }
        } else {
            let id = self.variables.len();
            let v = Rc::new(Variable::new(id, name.clone(), sort));
            if sort == Sort::String {
                // Create the len variable
                let len_name = self.len_var_name(name.as_str());
                let len_id = self.variables.len();
                let len_var = Rc::new(Variable::new(len_id, len_name.clone(), Sort::Int));
                self.variables.insert(len_name, len_var);
            }
            self.variables.insert(name, v.clone());
            Some(v)
        }
    }

    fn len_var_name(&self, name: &str) -> String {
        format!("{}__len", name)
    }

    /// For a string variable, returns a variable that represents the length of the string.
    /// Panics if the variable is not a string variable.
    pub fn get_len_var(&self, v: &Variable) -> &Rc<Variable> {
        assert_eq!(
            v.sort(),
            Sort::String,
            "Only a string variable has a length variable"
        );
        let len_name = self.len_var_name(v.name());
        self.variables.get(&len_name).unwrap()
    }

    pub fn new_temp_var(&mut self, sort: Sort) -> Rc<Variable> {
        let name = format!("__temp_{}", self.variables.len());
        let v = self.new_var(name.clone(), sort).unwrap();
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

    /// Returns an iterator over all integer variables.
    /// Includes temporary variables.
    pub fn string_vars(&self) -> impl Iterator<Item = &Rc<Variable>> + '_ {
        self.vars_with_sort(Sort::String)
    }

    /// Returns an iterator over all string variables and their length variables.
    pub fn string_len_vars(&self) -> impl Iterator<Item = (&Rc<Variable>, &Rc<Variable>)> + '_ {
        self.string_vars().map(|v| (v, self.get_len_var(v)))
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

    // pub fn ir_builder(&self) -> RefMut<IrBuilder> {
    //     self.ir_builder.borrow_mut()
    // }
}
