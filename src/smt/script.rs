use std::{
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use crate::{
    ast::Node,
    context::{Sorted, Variable},
    smt::escapce_smt_identifier_name,
};

use super::ToSmt;

#[derive(Debug, Default, Clone)]
pub struct Script {
    commands: Vec<Command>,
}

impl Script {
    pub fn declared_vars(&self) -> impl Iterator<Item = &Rc<Variable>> {
        self.commands.iter().filter_map(|cmd| match cmd {
            Command::DeclareConst(v) => Some(v),
            _ => None,
        })
    }

    pub fn push(&mut self, command: Command) {
        if let Command::NoOp = command {
            return;
        }
        self.commands.push(command);
    }

    pub fn commands(&self) -> &[Command] {
        &self.commands
    }

    pub fn iter(&self) -> impl Iterator<Item = &Command> {
        self.commands.iter()
    }

    pub fn iter_asserts(&self) -> impl Iterator<Item = &Node> {
        self.iter().filter_map(|cmd| match cmd {
            Command::Assert(expr) => Some(expr),
            _ => None,
        })
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
pub enum Command {
    Assert(Node),
    CheckSat,
    DeclareConst(Rc<Variable>),
    Echo(String),
    Exit,
    GetModel,
    SetLogic(String),
    NoOp,
}

impl Display for Command {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Command::Assert(node) => write!(f, "(assert {})", node.to_smt()),
            Command::CheckSat => write!(f, "(check-sat)"),
            Command::DeclareConst(v) => {
                write!(
                    f,
                    "(declare-const {} {})",
                    escapce_smt_identifier_name(v.name()),
                    v.sort()
                )
            }
            Command::Echo(message) => write!(f, "(echo \"{}\")", message),
            Command::Exit => write!(f, "(exit)"),
            Command::GetModel => write!(f, "(get-model)"),
            Command::SetLogic(logic) => write!(f, "(set-logic {})", logic),
            Command::NoOp => Ok(()),
        }
    }
}
