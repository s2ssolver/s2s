use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::ast::{Sort, Sorted, Variable};

#[derive(Default)]
pub struct Context {
    /// Manages the variables
    variables: HashMap<String, Rc<Variable>>,
    temp_vars: HashSet<Rc<Variable>>,
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
    pub fn get_len_var(&self, v: &Variable) -> Rc<Variable> {
        assert_eq!(
            v.sort(),
            Sort::String,
            "Only a string variable has a length variable"
        );
        let len_name = self.len_var_name(v.name());
        self.variables.get(&len_name).unwrap().clone()
    }

    pub fn new_temp_var(&mut self, sort: Sort) -> Rc<Variable> {
        let name = format!("__temp_{}", self.variables.len());
        let v = self.new_var(name.clone(), sort).unwrap();
        self.temp_vars.insert(v.clone());
        v
    }

    pub fn get_var(&self, name: &str) -> Option<Rc<Variable>> {
        self.variables.get(name).cloned()
    }
}
