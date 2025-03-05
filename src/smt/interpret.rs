use crate::{
    node::{Node, NodeManager},
    smt::{Script, SmtCommand},
    solver::Engine,
    Error, SolverOptions, SolverResult,
};

/// Interpreter for SMT-LIB scripts.
pub struct Interpreter<'a> {
    mngr: &'a mut NodeManager,

    engine: Engine,
    last_res: Option<SolverResult>,

    /// Assertion that have been pushed to the stack, but for which `check_sat` has not been called.
    /// Calling `check_sat` will pop all assertions from this stack and push them to the engine.
    assertion_stack: Vec<Node>,
}

impl<'a> Interpreter<'a> {
    pub fn new(options: SolverOptions, mngr: &'a mut NodeManager) -> Self {
        let engine = Engine::with_options(options.clone());
        Self {
            mngr,
            engine,
            last_res: None,
            assertion_stack: Vec::new(),
        }
    }

    pub fn run(&mut self, script: &Script) -> Result<(), Error> {
        for cmd in script.iter() {
            match cmd {
                SmtCommand::Assert(node) => {
                    self.assert(node);
                }
                SmtCommand::CheckSat => {
                    let res = self.check_sat()?;
                    println!("{}", res);
                    self.last_res = Some(res);
                }
                SmtCommand::Echo(msg) => {
                    println!("{}", msg);
                }
                SmtCommand::Exit => return Ok(()),
                SmtCommand::GetModel => {
                    if let Some(SolverResult::Sat(Some(m))) = &self.last_res {
                        println!("{}", m);
                    } else {
                        eprintln!("error: no model to get");
                    }
                }
                SmtCommand::DeclareConst(_, _) | SmtCommand::SetLogic(_) | SmtCommand::NoOp => (),
            }
        }
        Ok(())
    }

    pub fn assert(&mut self, node: &Node) {
        self.assertion_stack.push(node.clone());
    }

    pub fn check_sat(&mut self) -> Result<SolverResult, Error> {
        let root = self.mngr.and(std::mem::take(&mut self.assertion_stack));
        self.engine.solve(&root, self.mngr)
    }
}
