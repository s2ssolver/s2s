use std::cmp::max;

use indexmap::IndexMap;

use crate::ast::{Script, Sort, Sorted, Variable};

/// A problem instance, consisting of a script and options.
#[derive(Clone, Debug)]
pub struct Instance {
    /// The SMT script to solve
    script: Script,

    /// The maximum bound for any variable to check.
    /// If `None`, no bound is set, which will might in an infinite search if the instance is not satisfiable.
    /// If `Some(n)`, the solver will only check for a solution with a bound of `n`.
    /// If no solution is found with every variable bound to `n`, the solver will return `Unsat`.
    ubound: Option<usize>,

    /// The upper bound for each string variable to start the search with   
    start_bound: usize,

    print_model: bool,

    /// Terminate after preprocessing without solving the instance
    dry: bool,

    preprocess: bool,

    /// The set of variables, indexed by name
    vars: IndexMap<String, Variable>,
}

impl Instance {
    pub fn new(script: Script) -> Self {
        Instance {
            script,
            ubound: None,
            start_bound: 1,
            preprocess: true,
            vars: IndexMap::new(),
            print_model: false,
            dry: false,
        }
    }

    pub fn set_ubound(&mut self, bound: usize) {
        self.ubound = Some(bound);
    }

    pub fn set_lbound(&mut self, bound: usize) {
        self.start_bound = bound;
    }

    pub fn preprocess(&self) -> bool {
        self.preprocess
    }

    pub fn set_preprocess(&mut self, preprocess: bool) {
        self.preprocess = preprocess;
    }

    pub fn remove_bound(&mut self) {
        self.ubound = None;
    }

    pub fn get_script(&self) -> &Script {
        &self.script
    }

    pub fn get_script_mut(&mut self) -> &mut Script {
        &mut self.script
    }

    pub fn get_start_bound(&self) -> usize {
        max(self.start_bound, 1)
    }

    pub fn get_upper_threshold(&self) -> Option<usize> {
        self.ubound
    }

    pub fn set_print_model(&mut self, arg: bool) {
        self.print_model = arg;
    }

    pub fn get_print_model(&self) -> bool {
        self.print_model
    }

    /// Adds an existing variable to the manager, if it does not exist yet.
    /// If the variable is a string variable, also adds the length variable.
    ///
    /// # Panics
    ///
    /// Panics if a *different* variable with the same name already exists
    pub fn add_var(&mut self, var: Variable) {
        if let Some(v) = self.vars.get(var.name()) {
            if v != &var {
                panic!(
                    "Variable {} already exists with different value",
                    var.name()
                );
            }
            return;
        }
        if var.sort() == Sort::String {
            // also insert a integer variable representing the length of the string
            self.add_var(var.len_var().unwrap());
        }
        self.vars.insert(var.name().to_string(), var);
    }

    /// Returns an iterator over the variables of a certain sort.
    /// If `with_temps` is true, the iterator includes temporal variables.
    pub fn vars_of_sort(&self, sort: Sort) -> impl Iterator<Item = &Variable> {
        self.vars.values().filter(move |v| v.sort() == sort)
    }

    /// Returns an iterator over all variables.
    pub fn iter_vars(&self) -> impl Iterator<Item = &Variable> {
        self.vars.values()
    }

    /// Returns a variable by name, if it exists
    pub fn var_by_name(&self, name: &str) -> Option<&Variable> {
        self.vars.get(name)
    }

    pub fn dry_run(&self) -> bool {
        self.dry
    }

    pub fn set_dry_run(&mut self, dry: bool) {
        self.dry = dry;
    }
}
