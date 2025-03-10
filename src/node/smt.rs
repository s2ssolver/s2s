use super::Node;
use super::NodeKind;

use crate::smt::Command;
use crate::smt::Script;

pub fn to_script(node: &Node) -> Script {
    let mut script = Script::default();

    let vs = node.variables();
    for v in vs {
        let decl = Command::DeclareConst(v);
        script.push(decl);
    }

    let assertions = if *node.kind() == NodeKind::And {
        node.children().to_vec()
    } else {
        vec![node.clone()]
    };
    for assertion in assertions {
        let assert = Command::Assert(assertion);
        script.push(assert);
    }
    script.push(Command::CheckSat);

    script
}
