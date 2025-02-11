use std::fmt::{self, Display, Formatter};

use crate::node::{Node, NodeKind};

use super::{Sort, Symbol};

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

    pub fn iter_asserts(&self) -> impl Iterator<Item = &Node> {
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
    Assert(Node),
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
            SmtCommand::Assert(node) => write!(f, "(assert {})", node.to_smt()),
            SmtCommand::CheckSat => write!(f, "(check-sat)"),
            SmtCommand::DeclareConst(symbol, sort) => {
                write!(
                    f,
                    "(declare-const {} {})",
                    escapce_smt_identifier_name(symbol),
                    sort
                )
            }
            SmtCommand::Echo(message) => write!(f, "(echo \"{}\")", message),
            SmtCommand::Exit => write!(f, "(exit)"),
            SmtCommand::GetModel => write!(f, "(get-model)"),
            SmtCommand::SetLogic(logic) => write!(f, "(set-logic {})", logic),
            SmtCommand::NoOp => Ok(()),
        }
    }
}

trait ToSmt {
    fn to_smt(&self) -> String;
}

impl ToSmt for Node {
    fn to_smt(&self) -> String {
        if self.children().is_empty() {
            return self.kind().to_smt();
        } else {
            let ch = self
                .children()
                .iter()
                .map(|c| c.to_smt())
                .collect::<Vec<_>>()
                .join(" ");
            format!("({} {})", self.kind().to_smt(), ch)
        }
    }
}

impl ToSmt for NodeKind {
    fn to_smt(&self) -> String {
        match self {
            NodeKind::Bool(true) => "true".to_string(),
            NodeKind::Bool(false) => "false".to_string(),
            NodeKind::String(s) => format!("\"{}\"", escape_smt_string(s)),
            NodeKind::Int(i) => i.to_string(),
            NodeKind::Regex(regex) => regulaer::parse::to_smt(regex),
            NodeKind::Variable(rc) => escapce_smt_identifier_name(rc.name()),
            NodeKind::Or => "or".to_string(),
            NodeKind::And => "and".to_string(),
            NodeKind::Imp => "=>".to_string(),
            NodeKind::Equiv => "=".to_string(),
            NodeKind::Not => "not".to_string(),
            NodeKind::Ite => "ite".to_string(),
            NodeKind::Eq => "=".to_string(),
            NodeKind::Concat => "str.++".to_string(),
            NodeKind::Length => "str.len".to_string(),
            NodeKind::InRe => "str.in_re".to_string(),
            NodeKind::PrefixOf => "str.prefixof".to_string(),
            NodeKind::SuffixOf => "str.suffixof".to_string(),
            NodeKind::Contains => "str.contains".to_string(),
            NodeKind::Add => "+".to_string(),
            NodeKind::Neg | NodeKind::Sub => "-".to_string(),
            NodeKind::Mul => "*".to_string(),
            NodeKind::Lt => "<".to_string(),
            NodeKind::Le => "<=".to_string(),
            NodeKind::Gt => ">".to_string(),
            NodeKind::Ge => ">=".to_string(),
            NodeKind::Literal(_) => unreachable!(),
        }
    }
}

const SMT_MAX_CHAR: u32 = 0x2FFFF;
fn escape_smt_string(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c as u32 > SMT_MAX_CHAR {
                c.escape_unicode().to_string()
            } else {
                c.to_string()
            }
        })
        .collect()
}

fn escapce_smt_identifier_name(name: &str) -> String {
    if name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        name.to_string()
    } else {
        format!("|{}|", name)
    }
}
