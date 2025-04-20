//! SMT-LIB representation of quantifier free first-order formulas for the theory of strings.

/// Errors that can occur while working with SMT-LIB formulas.
mod error;

mod convert;

/// Representation of SMT-LIB scripts.
mod script;

mod interpret;

//pub use ast::*;
// pub use builder::AstBuilder;
pub use error::*;

pub use script::*;

pub use interpret::Interpreter;
use smt2parser::concrete::SyntaxBuilder;

use crate::node::{Node, NodeKind, NodeManager, Sort, Sorted, VarSubstitution};

pub fn parse_script(
    smt: impl std::io::BufRead,

    mngr: &mut NodeManager,
) -> Result<Script, AstError> {
    let cmds = smt2parser::CommandStream::new(smt, SyntaxBuilder, None);
    let mut converter = convert::Converter::new(mngr);
    let mut script = Script::default();
    for cmd in cmds {
        script.push(converter.convert(cmd?)?);
    }
    Ok(script)
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

impl ToSmt for VarSubstitution {
    fn to_smt(&self) -> String {
        let mut result = String::new();
        result.push_str("(\n");
        for (var, node) in self.iter() {
            result.push_str(&format!(
                "(define-fun {} () {} {})\n",
                escapce_smt_identifier_name(var.name()),
                var.sort().to_smt(),
                node.to_smt()
            ));
        }
        result.push_str(")");
        result
    }
}

impl ToSmt for Sort {
    fn to_smt(&self) -> String {
        match self {
            Sort::Int => "Int",
            Sort::String => "String",
            Sort::RegLan => "RegLan",
            Sort::Bool => "Bool",
        }
        .to_string()
    }
}

fn escapce_smt_identifier_name(name: &str) -> String {
    if name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        name.to_string()
    } else {
        format!("|{}|", name)
    }
}
