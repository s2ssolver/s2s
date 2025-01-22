use crate::{
    node::{Node, NodeManager},
    smt::{Script, SmtCommand},
    solver::Engine,
    Error, SolverOptions, SolverResult,
};

pub struct Interpreter<'a> {
    mngr: &'a mut NodeManager,
    _options: SolverOptions,

    engine: Engine,
    last_res: Option<SolverResult>,

    assertions: Vec<Node>,
}

impl<'a> Interpreter<'a> {
    pub fn new(options: SolverOptions, mngr: &'a mut NodeManager) -> Self {
        let engine = Engine::with_options(options.clone());
        Self {
            mngr,
            _options: options,
            engine,
            last_res: None,
            assertions: Vec::new(),
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
                    // transfer the assertions to the solver and check sat
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
        self.assertions.push(node.clone());
    }

    pub fn check_sat(&mut self) -> Result<SolverResult, Error> {
        let root = self.mngr.and(std::mem::take(&mut self.assertions));
        //self.solver.solve(&root, self.mngr)
        self.engine.solve(&root, self.mngr)
    }
}
