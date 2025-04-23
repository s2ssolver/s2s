use crate::{
    engine::Engine,
    ast::{Node, NodeManager},
    smt::{Command, Script, ToSmt},
    Error, SolverAnswer, SolverOptions,
};

/// Interpreter for SMT-LIB scripts.
pub struct Interpreter<'a> {
    mngr: &'a mut NodeManager,
    options: SolverOptions,
    engine: Engine,
}

impl<'a> Interpreter<'a> {
    pub fn new(options: SolverOptions, mngr: &'a mut NodeManager) -> Self {
        let engine = Engine::with_options(options.clone());
        Self {
            mngr,
            options,
            engine,
        }
    }

    pub fn run(&mut self, script: &Script) -> Result<(), Error> {
        for cmd in script.iter() {
            match cmd {
                Command::Assert(fm) => {
                    self.assert(fm);
                }
                Command::CheckSat => {
                    let res = self.check_sat()?;
                    println!("{}", res);
                    if self.options.get_model {
                        self.print_model();
                    }
                }
                Command::Echo(msg) => {
                    println!("{}", msg);
                }
                Command::Exit => return Ok(()),
                Command::GetModel => self.print_model(),
                Command::DeclareConst(_) | Command::SetLogic(_) | Command::NoOp => (),
            }
        }
        Ok(())
    }

    fn print_model(&self) {
        if let SolverAnswer::Sat(Some(m)) = &self.engine.get_result() {
            println!("{}", m.to_smt());
        } else {
            eprintln!("error: no model to get");
        }
    }

    pub fn assert(&mut self, node: &Node) {
        self.engine.assert(node);
    }

    pub fn check_sat(&mut self) -> Result<SolverAnswer, Error> {
        // let root = self.mngr.and(std::mem::take(&mut self.assertion_stack));
        // self.engine.solve(&root, self.mngr)
        self.engine.check(self.mngr)?;
        Ok(self.engine.get_result().clone())
    }
}
