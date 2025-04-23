use crate::{
    ast::Node,
    context::Context,
    engine::Engine,
    smt::{Command, Script, ToSmt},
    Error, SolverAnswer, SolverOptions,
};

/// Interpreter for SMT-LIB scripts.
pub struct Interpreter<'a> {
    ctx: &'a mut Context,
    options: SolverOptions,
    engine: Engine,
}

impl<'a> Interpreter<'a> {
    pub fn new(options: SolverOptions, ctx: &'a mut Context) -> Self {
        let engine = Engine::with_options(options.clone());
        Self {
            ctx,
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
        // let root = self.ctx.ast().and(std::mem::take(&mut self.assertion_stack));
        // self.engine.solve(&root, self.ctx)
        self.engine.check(self.ctx)?;
        Ok(self.engine.get_result().clone())
    }
}
