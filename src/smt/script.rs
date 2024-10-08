use std::fmt::{self, Display, Formatter};

use super::{ast::Expression, Sort, Symbol};

#[derive(Debug, Default, Clone)]
pub struct Script {
    commands: Vec<SmtCommand>,
}

impl Script {
    pub fn declared_vars(&self) -> impl Iterator<Item = (&Symbol, &Sort)> {
        self.commands.iter().filter_map(|cmd| match cmd {
            SmtCommand::DeclareConst(symbol, sort) => Some((symbol, sort)),
            _ => None,
        })
    }

    pub fn push(&mut self, command: SmtCommand) {
        if let SmtCommand::NoOp = command {
            return;
        }
        self.commands.push(command);
    }

    pub fn commands(&self) -> &[SmtCommand] {
        &self.commands
    }

    pub fn iter(&self) -> impl Iterator<Item = &SmtCommand> {
        self.commands.iter()
    }

    pub fn iter_asserts(&self) -> impl Iterator<Item = &Expression> {
        self.iter().filter_map(|cmd| match cmd {
            SmtCommand::Assert(expr) => Some(expr),
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
pub enum SmtCommand {
    Assert(Expression),
    CheckSat,
    DeclareConst(Symbol, Sort),
    Echo(String),
    Exit,
    GetModel,
    SetLogic(Symbol),
    NoOp,
}

impl Display for SmtCommand {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SmtCommand::Assert(expr) => write!(f, "(assert {})", expr),
            SmtCommand::CheckSat => write!(f, "(check-sat)"),
            SmtCommand::DeclareConst(symbol, sort) => {
                write!(f, "(declare-const {} {})", symbol, sort)
            }
            SmtCommand::Echo(message) => write!(f, "(echo \"{}\")", message),
            SmtCommand::Exit => write!(f, "(exit)"),
            SmtCommand::GetModel => write!(f, "(get-model)"),
            SmtCommand::SetLogic(logic) => write!(f, "(set-logic {})", logic),
            SmtCommand::NoOp => Ok(()),
        }
    }
}
