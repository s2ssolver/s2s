use std::{
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use crate::repr::{Sorted, Variable};

use super::expr::Expression;

#[derive(Debug, Default, Clone)]
pub struct Script {
    commands: Vec<SmtCommand>,
}

impl Script {
    /* Constructors for commands */
    pub fn declare_var(&mut self, var: Rc<Variable>) {
        self.push(SmtCommand::DeclareConst(var));
    }

    pub fn assert(&mut self, expr: Rc<Expression>) {
        self.push(SmtCommand::Assert(expr));
    }

    pub fn set_logic(&mut self, logic: String) {
        self.push(SmtCommand::SetLogic(logic));
    }

    pub fn check_sat(&mut self) {
        self.push(SmtCommand::CheckSat);
    }

    pub fn get_model(&mut self) {
        if let Some(SmtCommand::GetModel) = self.commands.last() {
            return;
        }
        self.push(SmtCommand::GetModel);
    }

    pub fn exit(&mut self) {
        self.push(SmtCommand::Exit);
    }

    pub fn declared_vars(&self) -> impl Iterator<Item = &Rc<Variable>> {
        self.commands.iter().filter_map(|cmd| match cmd {
            SmtCommand::DeclareConst(var) => Some(var),
            _ => None,
        })
    }

    fn push(&mut self, command: SmtCommand) {
        self.commands.push(command);
    }

    pub fn commands(&self) -> &[SmtCommand] {
        &self.commands
    }

    pub fn iter(&self) -> impl Iterator<Item = &SmtCommand> {
        self.commands.iter()
    }

    pub fn iter_asserts(&self) -> impl Iterator<Item = &Rc<Expression>> {
        self.iter().filter_map(|cmd| match cmd {
            SmtCommand::Assert(expr) => Some(expr),
            _ => None,
        })
    }

    /// Creates a new script with the given assertions.
    /// Keeps the other commands as they are.
    /// The assertions are expected to be in the same order as the original script.
    /// Panics if the number of assertions does not match the original script.
    pub fn replace_assertions(&self, assertions: Vec<Rc<Expression>>) -> Self {
        debug_assert!(assertions.len() == self.iter_asserts().count());

        let mut replaced = Script::default();
        let mut assertions = assertions.into_iter();
        for cmnd in self.commands() {
            match cmnd {
                SmtCommand::Assert(_) => {
                    let a = assertions.next().unwrap();

                    replaced.assert(a);
                }
                SmtCommand::CheckSat => replaced.check_sat(),
                SmtCommand::DeclareConst(c) => replaced.declare_var(c.clone()),
                SmtCommand::Exit => replaced.exit(),
                SmtCommand::GetModel => replaced.get_model(),
                SmtCommand::SetLogic(s) => replaced.set_logic(s.clone()),
            }
        }
        replaced
    }
}

impl Display for Script {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for command in self.commands() {
            writeln!(f, "{}", command)?;
        }
        Ok(())
    }
}

/// The currently supported SMT2 commands.
#[derive(Debug, Clone)]
pub enum SmtCommand {
    Assert(Rc<Expression>),
    CheckSat,
    DeclareConst(Rc<Variable>),
    Exit,
    GetModel,
    SetLogic(String),
}

impl Display for SmtCommand {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SmtCommand::Assert(expr) => write!(f, "(assert {})", expr),
            SmtCommand::CheckSat => write!(f, "(check-sat)"),
            SmtCommand::DeclareConst(var) => {
                write!(f, "(declare-const {} {})", var.name(), var.sort())
            }

            SmtCommand::Exit => write!(f, "(exit)"),
            SmtCommand::GetModel => write!(f, "(get-model)"),
            SmtCommand::SetLogic(logic) => write!(f, "(set-logic {})", logic),
        }
    }
}
