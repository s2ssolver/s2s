use std::{
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use crate::node::{Node, NodeKind, Sorted, Variable};

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

trait ToSmt {
    fn to_smt(&self) -> String;
}

impl ToSmt for Node {
    fn to_smt(&self) -> String {
        if self.children().is_empty() {
            self.kind().to_smt()
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
            NodeKind::String(s) => format!("\"{}\"", s),
            NodeKind::Int(i) => {
                if *i >= 0 {
                    i.to_string()
                } else {
                    format!("(- {})", -i)
                }
            }
            NodeKind::Regex(regex) => format!("{}", regex),
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
            NodeKind::SubStr => "str.substr".to_string(),
            NodeKind::At => "str.at".to_string(),
            NodeKind::Replace => "str.replace".to_string(),
            NodeKind::ReplaceAll => "str.replace_all".to_string(),
            NodeKind::ToInt => "str.to_int".to_string(),
            NodeKind::FromInt => "str.from_int".to_string(),
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

fn escapce_smt_identifier_name(name: &str) -> String {
    if name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        name.to_string()
    } else {
        format!("|{}|", name)
    }
}
