use crate::{
    engine::Engine,
    node::{Node, NodeManager},
    smt::{Command, Script},
    Error, SolverAnswer, SolverOptions,
};

/// Interpreter for SMT-LIB scripts.
pub struct Interpreter<'a> {
    mngr: &'a mut NodeManager,

    engine: Engine,
}

impl<'a> Interpreter<'a> {
    pub fn new(options: SolverOptions, mngr: &'a mut NodeManager) -> Self {
        let engine = Engine::with_options(options.clone());
        Self { mngr, engine }
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
                }
                Command::Echo(msg) => {
                    println!("{}", msg);
                }
                Command::Exit => return Ok(()),
                Command::GetModel => {
                    if let SolverAnswer::Sat(Some(m)) = &self.engine.get_result() {
                        println!("{}", m);
                    } else {
                        eprintln!("error: no model to get");
                    }
                }
                Command::DeclareConst(_) | Command::SetLogic(_) | Command::NoOp => (),
            }
        }
        Ok(())
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
