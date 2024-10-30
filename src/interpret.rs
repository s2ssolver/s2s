use crate::{
    node::NodeManager,
    smt::{Script, SmtCommand},
    Error, Solver, SolverOptions, SolverResult,
};

pub(crate) struct Interpreter<'a> {
    script: Script,
    mngr: &'a mut NodeManager,
    options: SolverOptions,
    solver: Solver,
    last_res: Option<SolverResult>,
}

impl<'a> Interpreter<'a> {
    pub(crate) fn new(script: Script, options: SolverOptions, mngr: &'a mut NodeManager) -> Self {
        let solver = Solver::with_options(options.clone());
        Self {
            script,
            mngr,
            solver,
            options,
            last_res: None,
        }
    }

    pub(crate) fn run(&mut self) -> Result<(), Error> {
        let mut assertions = Vec::new();
        for cmd in self.script.iter() {
            match cmd {
                SmtCommand::Assert(_) => unreachable!(),
                SmtCommand::AssertNew(node) => {
                    assertions.push(node.clone());
                }
                SmtCommand::CheckSat => {
                    let root = self.mngr.and(std::mem::take(&mut assertions));
                    let res = self.solver.solve(&root, self.mngr)?;
                    println!("{}", res);
                    self.last_res = Some(res);
                    // transfer the assertions to the solver and check sat
                }
                SmtCommand::Echo(msg) => {
                    println!("{}", msg);
                }
                SmtCommand::Exit => return Ok(()),
                SmtCommand::GetModel => {
                    if let Some(res) = &self.last_res {
                        if let SolverResult::Sat(Some(m)) = res {
                            println!("{}", m);
                        } else {
                            eprintln!("error: no model to get");
                        }
                    } else {
                        eprintln!("error: no model to get");
                    }
                }
                SmtCommand::DeclareConst(_, _) | SmtCommand::SetLogic(_) | SmtCommand::NoOp => (),
            }
        }
        Ok(())
    }
}
