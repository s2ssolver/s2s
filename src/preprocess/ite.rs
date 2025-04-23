//! Preprecessing ITE nodes.

use std::rc::Rc;

use indexmap::IndexMap;

use crate::ast::{Node, NodeKind, NodeManager};
use crate::context::{Sorted, Variable};

#[derive(Default)]
pub struct ITEHandler {
    defs: IndexMap<Node, Rc<Variable>>,
}

impl ITEHandler {
    /// Eliminates ITE nodes from the given node.
    /// Returns a new node with all ITE nodes removed.
    /// The returned node is **not** necessarily in BNF, a separate conversion is required after this.
    pub fn elim_ite(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        // Remove all ITE nodes from the given node
        let removed = self.remove_ite(node, mngr);

        // Handle the definitions
        let mut defs = self.rewrite_defs(mngr);
        if defs.is_empty() {
            removed
        } else {
            defs.push(removed);
            mngr.and(defs)
        }
    }

    /// Removes ITE nodes from the given node.
    fn remove_ite(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        // Remove ITE from children
        let ch_rw = node
            .children()
            .iter()
            .map(|c| self.remove_ite(c, mngr))
            .collect::<Vec<_>>();

        // If the node is an ITE, rewrite it
        let new_node = mngr.create_node(node.kind().clone(), ch_rw);

        if *new_node.kind() == NodeKind::Ite {
            if let Some(rw) = self.pure_boolean_ite(&new_node, mngr) {
                rw
            } else {
                let tmpv = self.define_ite(&new_node, mngr);
                mngr.var(tmpv.clone())
            }
        } else {
            new_node
        }
    }

    /// Defines an ITE node `ITE(c, t, e)` as a new variable `V = ITE(c, t, e)` and returns `V`.
    /// `V` has the same sort as `t` and `e`.
    /// If the ITE node has already been defined, returns the existing variable.
    fn define_ite(&mut self, node: &Node, mngr: &mut NodeManager) -> Rc<Variable> {
        debug_assert!(
            *node.kind() == NodeKind::Ite,
            "Expected ITE node, got {:?}",
            node
        );
        if let Some(v) = self.defs.get(node) {
            return v.clone();
        }

        let ite_cond = node.children()[0].clone();
        let ite_then = node.children()[1].clone();
        let ite_else = node.children()[2].clone();
        debug_assert!(
            ite_cond.sort().is_bool(),
            "Expected boolean sort, got {:?}",
            ite_cond.sort()
        );
        debug_assert_eq!(
            ite_then.sort(),
            ite_else.sort(),
            "Expected same sort for then and else, got {:?} and {:?}",
            ite_then.sort(),
            ite_else.sort()
        );
        let sort = ite_then.sort();

        let v = mngr.temp_var(sort);
        self.defs.insert(node.clone(), v.clone());
        v
    }

    fn rewrite_defs(&mut self, mngr: &mut NodeManager) -> Vec<Node> {
        let defs = std::mem::take(&mut self.defs);

        // these are all of the form `V = ITE(c, t, e)`.
        // we need to rewrite them as `c -> V = t /\ !c -> V = e`.
        let mut rew = Vec::with_capacity(defs.len());
        for (ite, v) in defs {
            let ite_cond = ite.children()[0].clone();
            let ite_then = ite.children()[1].clone();
            let ite_else = ite.children()[2].clone();
            debug_assert_eq!(v.sort(), ite_then.sort());
            debug_assert_eq!(v.sort(), ite_else.sort());

            let v = mngr.var(v);

            let (eq_then, eq_else) = if v.sort().is_bool() {
                (
                    mngr.equiv(v.clone(), ite_then),
                    mngr.equiv(v.clone(), ite_else),
                )
            } else {
                (mngr.eq(v.clone(), ite_then), mngr.eq(v.clone(), ite_else))
            };

            let ltf = mngr.imp(ite_cond.clone(), eq_then);
            let not_ite_cond = mngr.not(ite_cond);
            let nltr = mngr.imp(not_ite_cond, eq_else);

            let rewrt = mngr.and(vec![ltf, nltr]);
            rew.push(rewrt);
        }
        rew
    }

    /// If the given ITE node is pure boolean, rewrites it as `c -> t /\ !c -> e`. Returns the rewritten node.
    /// If the ITE node is not pure boolean, returns `None`.
    /// Purely boolean means that the node is of the form `ITE(c, t, e)` where `c`, `t`, and `e` are Boolean.
    pub fn pure_boolean_ite(&self, ite: &Node, mngr: &mut NodeManager) -> Option<Node> {
        debug_assert!(
            *ite.kind() == NodeKind::Ite,
            "Expected ITE node, got {:?}",
            ite
        );

        let c = &ite.children()[0];
        let t = &ite.children()[1];
        let e = &ite.children()[2];

        debug_assert!(
            c.sort().is_bool(),
            "Expected boolean sort, got {:?}",
            c.sort()
        );
        debug_assert_eq!(t.sort(), e.sort());

        if t.sort().is_bool() {
            let ltf = mngr.imp(c.clone(), t.clone());
            let not_c = mngr.not(c.clone());
            let nltr = mngr.imp(not_c, e.clone());
            let rewrt = mngr.and(vec![ltf, nltr]);
            Some(rewrt)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::NodeKind;

    fn setup() -> NodeManager {
        NodeManager::default()
    }

    #[test]
    fn test_pure_boolean_ite() {
        let mut mngr = setup();
        let c = mngr.bool_var("c").unwrap();
        let c = mngr.var(c.clone());
        let t = mngr.bool_var("t").unwrap();
        let t = mngr.var(t.clone());
        let e = mngr.bool_var("e").unwrap();
        let e = mngr.var(e.clone());
        let ite = mngr.ite(c.clone(), t.clone(), e.clone());

        let handler = ITEHandler::default();
        let rewritten = handler.pure_boolean_ite(&ite, &mut mngr).unwrap();

        // Expected: (c → t) ∧ (¬c → e)
        let not_c = mngr.not(c.clone());
        let imp1 = mngr.imp(c.clone(), t.clone());
        let imp2 = mngr.imp(not_c, e.clone());
        let expected = mngr.and(vec![imp1, imp2]);

        assert_eq!(rewritten, expected,);
    }

    #[test]
    fn test_define_ite_creates_variable() {
        let mut mngr = setup();
        let mut handler = ITEHandler::default();

        let c = mngr.bool_var("cond").unwrap();
        let c = mngr.var(c.clone());
        let t = mngr.const_int(1);
        let e = mngr.const_int(2);
        let ite = mngr.ite(c.clone(), t.clone(), e.clone());

        let v = handler.define_ite(&ite, &mut mngr);
        let v_node = mngr.var(v.clone());

        assert_eq!(v_node.sort(), t.sort());
        assert!(handler.defs.contains_key(&ite));
    }

    #[test]
    fn test_elim_ite_creates_definition() {
        let mut mngr = setup();
        let mut handler = ITEHandler::default();

        let c = mngr.bool_var("cond").unwrap();
        let c = mngr.var(c.clone());
        let t = mngr.const_int(42);
        let e = mngr.const_int(0);
        let ite = mngr.ite(c.clone(), t.clone(), e.clone());

        let one = mngr.const_int(1);

        // (= ITE(c, 42, 0), 1)
        let root = mngr.eq(ite.clone(), one.clone());

        let rewritten = handler.elim_ite(&root, &mut mngr);

        // rewritten should  be of the form: 1=temp /\ (c -> 42=temp) /\ (!c ->  0 = temp)
        assert_eq!(rewritten.kind(), &NodeKind::And);
        let children = rewritten.children();
        assert_eq!(children.len(), 3);
        assert_eq!(children[0].kind(), &NodeKind::Eq);
        assert_eq!(children[1].kind(), &NodeKind::Imp);
        assert_eq!(children[2].kind(), &NodeKind::Imp);

        assert_eq!(children[0].children()[0], one);
        if let NodeKind::Variable(temp_var) = children[0].children()[1].kind() {
            let temp_var = mngr.var(temp_var.clone());
            assert_eq!(children[0].children()[0], one.clone());
            assert_eq!(children[1].kind(), &NodeKind::Imp);
            assert_eq!(children[1].children()[0], c);
            assert_eq!(children[1].children()[1].kind(), &NodeKind::Eq);
            assert_eq!(children[1].children()[1].children()[0], t);
            assert_eq!(children[1].children()[1].children()[1], temp_var);

            assert_eq!(children[2].kind(), &NodeKind::Imp);
            assert_eq!(children[2].children()[0].kind(), &NodeKind::Not);
            assert_eq!(children[2].children()[0].children()[0], c);
            assert_eq!(children[2].children()[1].kind(), &NodeKind::Eq);
            assert_eq!(children[2].children()[1].children()[0], e);
            assert_eq!(children[2].children()[1].children()[1], temp_var);
        } else {
            unreachable!()
        }
    }
}
