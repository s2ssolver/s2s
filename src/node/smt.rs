use super::Node;
use super::NodeKind;
use super::Sorted;

use crate::smt::Script;
use crate::smt::SmtCommand;

pub fn to_script(node: &Node) -> Script {
    let mut script = Script::default();

    let vs = node.variables();
    for v in vs {
        let decl = SmtCommand::DeclareConst(v.name().to_string(), v.sort().into());
        script.push(decl);
    }

    let assertions = if *node.kind() == NodeKind::And {
        node.children().to_vec()
    } else {
        vec![node.clone()]
    };
    for assertion in assertions {
        let assert = SmtCommand::Assert(assertion);
        script.push(assert);
    }
    script.push(SmtCommand::CheckSat);

    script
}
