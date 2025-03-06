use std::collections::HashMap;

use indexmap::IndexMap;
use regulaer::{
    alph::CharRange,
    re::{ReBuilder, RegOp, Regex, RegexProps, Word},
};

use crate::{
    node::{Node, NodeKind, NodeManager},
    smt::smt_max_char,
};

#[derive(Default)]
pub struct ReCompRemover {
    cache: IndexMap<Regex, Regex>,
    range_cache: HashMap<CharRange, Regex>,
}

impl ReCompRemover {
    pub fn remove_comps(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        match node.kind() {
            NodeKind::Regex(regex) => {
                let re = self.remove_comp_re(regex, mngr.re_builder());
                mngr.const_regex(re)
            }
            NodeKind::Literal(_) => unreachable!(),
            _ => {
                let kind = node.kind().clone();
                let children = node
                    .children()
                    .iter()
                    .map(|child| self.remove_comps(child, mngr))
                    .collect();
                mngr.create_node(kind, children)
            }
        }
    }

    fn remove_comp_re(&mut self, re: &Regex, builder: &mut ReBuilder) -> Regex {
        if let Some(cc) = self.cache.get(re) {
            return cc.clone();
        }

        let result = if !re.contains_comp() {
            return re.clone();
        } else {
            match re.op() {
                RegOp::Comp(comped) => match comped.op() {
                    RegOp::Const(w) => self.comp_word(w.clone(), builder),
                    RegOp::None => builder.all(),
                    RegOp::All => builder.none(),
                    RegOp::AllChar => builder.epsilon(),
                    RegOp::Union(rs) => self.comp_union(rs.clone(), builder),
                    RegOp::Inter(rs) => self.comp_inter(rs.clone(), builder),
                    RegOp::Opt(r) => {
                        // Comp(Opt(A)) = Comp(A | epsilon) = Comp(A) & Comp(epsilon)

                        let comp_r = self.remove_comp_re(r, builder);
                        let comp_epsilon = self.comp_empty_word(builder);
                        builder.inter(vec![comp_r, comp_epsilon])
                    }
                    RegOp::Range(r) => self.comp_range(*r, builder),
                    RegOp::Comp(r) => r.clone(), // double negation
                    RegOp::Diff(r1, r2) => {
                        //comp(a-b) = comp(a & comp(b)) = comp(a) | b
                        let lhs = self.remove_comp_re(r1, builder);
                        let rhs = self.remove_comp_re(r2, builder);
                        builder.union(vec![lhs, rhs])
                    }
                    _ => unimplemented!("Unsupported complement operation: {}", comped),
                },
                RegOp::Diff(r1, r2) => self.rewrite_diff(r1.clone(), r2.clone(), builder),
                RegOp::Concat(rs) => {
                    let rs = rs.iter().map(|r| self.remove_comp_re(r, builder)).collect();
                    builder.concat(rs)
                }
                RegOp::Union(rs) => {
                    let rs = rs.iter().map(|r| self.remove_comp_re(r, builder)).collect();
                    builder.union(rs)
                }
                RegOp::Inter(rs) => {
                    let rs = rs.iter().map(|r| self.remove_comp_re(r, builder)).collect();
                    builder.inter(rs)
                }
                RegOp::Star(r) => {
                    let rr = self.remove_comp_re(r, builder);
                    builder.star(rr)
                }
                RegOp::Plus(r) => {
                    let rr = self.remove_comp_re(r, builder);
                    builder.plus(rr)
                }
                RegOp::Opt(r) => {
                    let rr = self.remove_comp_re(r, builder);
                    builder.opt(rr)
                }
                RegOp::Pow(r, e) => {
                    let rr = self.remove_comp_re(r, builder);
                    builder.pow(rr, *e)
                }
                RegOp::Loop(r, l, u) => {
                    let rr = self.remove_comp_re(r, builder);
                    builder.loop_(rr, *l, *u)
                }
                _ => re.clone(),
            }
        };
        self.cache.insert(re.clone(), result.clone());
        result
    }

    fn smt_all(&self) -> CharRange {
        CharRange::new(0 as char, smt_max_char())
    }

    // r1 - r2 => r1 & ~r2
    fn rewrite_diff(&mut self, r1: Regex, r2: Regex, builder: &mut ReBuilder) -> Regex {
        let r2comp = builder.comp(r2.clone());
        let r = builder.inter(vec![r1.clone(), r2comp]);
        self.remove_comp_re(&r, builder)
    }

    /// Comp(A|B) = Comp(A) & Comp(B)
    fn comp_union(&mut self, rs: Vec<Regex>, builder: &mut ReBuilder) -> Regex {
        let rs = rs.into_iter().map(|r| builder.comp(r)).collect();
        let as_inter = builder.inter(rs);
        self.remove_comp_re(&as_inter, builder)
    }

    /// Comp(A&B) = Comp(A) | Comp(B)
    fn comp_inter(&mut self, rs: Vec<Regex>, builder: &mut ReBuilder) -> Regex {
        let rs = rs.into_iter().map(|r| builder.comp(r)).collect();
        let as_union = builder.union(rs);
        self.remove_comp_re(&as_union, builder)
    }

    fn comp_empty_word(&self, builder: &mut ReBuilder) -> Regex {
        builder.plus(builder.any_char())
    }

    fn comp_word(&mut self, w: Word, builder: &mut ReBuilder) -> Regex {
        if w.is_empty() {
            self.comp_empty_word(builder)
        } else {
            let a = w.first().unwrap();
            let v = w.drop(1);

            // \epsi | ((comp a). ALL) | (a . (comp v))

            let a_comp = self.comp_char(a, builder);
            let a_comp_all = builder.concat(vec![a_comp, builder.all()]);
            let b_comp = self.comp_word(v, builder);

            let re_a = builder.word(a.into());
            let a_bcomp = builder.concat(vec![re_a, b_comp]);

            builder.union(vec![builder.epsilon(), a_comp_all, a_bcomp])
        }
    }

    fn comp_char(&mut self, a: char, builder: &mut ReBuilder) -> Regex {
        let r = CharRange::singleton(a);
        self.comp_range(r, builder)
    }

    fn comp_range(&mut self, r: CharRange, builder: &mut ReBuilder) -> Regex {
        if let Some(re) = self.range_cache.get(&r) {
            return re.clone();
        }
        if r.is_empty() {
            return builder.any_char();
        }
        let diff_r = self.smt_all().difference(&r);
        let diff_r = diff_r
            .into_iter()
            .map(|r| builder.range(r.start(), r.end()))
            .collect();
        let u = builder.union(diff_r);
        self.range_cache.insert(r, u.clone());
        u
    }
}

#[cfg(test)]
mod test {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use regulaer::{
        alph::CharRange,
        re::{ReBuilder, RegOp},
    };

    use crate::smt::smt_max_char;

    use super::ReCompRemover;

    #[test]
    fn re_comp_canonicalize_char() {
        let mut comp = ReCompRemover::default();
        let mut builder = ReBuilder::default();

        match comp.comp_char('a', &mut builder).op() {
            regulaer::re::RegOp::Union(items) => {
                assert_eq!(
                    items[0],
                    builder.range(0 as char, (('a' as u8) - 1) as char)
                );
                assert_eq!(items[1], builder.range('b', smt_max_char()));
            }
            _ => unreachable!(),
        }

        let comped = comp.comp_char(0 as char, &mut builder);
        match comped.op() {
            regulaer::re::RegOp::Range(r) => {
                assert_eq!(*r, CharRange::new(1 as char, smt_max_char()));
            }
            _ => unreachable!("Expected range got {}", comped),
        }
    }

    #[quickcheck]
    fn re_comp_canonicalize_range_non_empty(l: u8, u: u8) -> TestResult {
        if l >= u || u == u8::MAX {
            return TestResult::discard();
        }

        let mut comp = ReCompRemover::default();
        let mut builder = ReBuilder::default();

        match comp
            .comp_range(CharRange::new(l as char, u as char), &mut builder)
            .op()
        {
            regulaer::re::RegOp::Union(items) => {
                assert_eq!(items[0], builder.range(0 as char, (l - 1) as char));
                assert_eq!(items[1], builder.range((u + 1) as char, smt_max_char()));
            }
            RegOp::Range(r) => {
                assert_eq!(l, 0);
                assert_eq!(r.start(), (u + 1) as char);
            }
            _ => unreachable!(),
        }
        TestResult::passed()
    }

    #[quickcheck]
    fn re_comp_canonicalize_range_empty(l: u8, u: u8) -> TestResult {
        if l <= u {
            return TestResult::discard();
        }

        let mut comp = ReCompRemover::default();
        let mut builder = ReBuilder::default();

        let r = comp.comp_range(CharRange::new(l as char, u as char), &mut builder);
        if let RegOp::AllChar = r.op() {
            TestResult::passed()
        } else {
            panic!("Expected empty range to be represented as AllChar but got {r}",);
        }
    }

    #[test]
    fn re_comp_canonicalize_empty_word() {
        let mut comp = ReCompRemover::default();

        let mut builder = ReBuilder::default();
        let w = "".chars().collect();
        let r = comp.comp_word(w, &mut builder);
        assert_eq!(r, builder.plus(builder.any_char()));
    }
}
