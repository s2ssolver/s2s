use std::collections::HashMap;

use indexmap::IndexMap;
use smt_str::{
    alphabet::CharRange,
    re::{ReBuilder, ReOp, Regex},
    SmtChar, SmtString,
};

use smallvec::smallvec;

/// Tries to eliminate complement operations from the all regexes in the AST.
#[derive(Default)]
pub struct ReCompRemover {
    cache: IndexMap<Regex, Regex>,
    range_cache: HashMap<CharRange, Regex>,
}

impl ReCompRemover {
    /// Aplies the following rewerites to the regex:
    ///
    /// - comp(A|B) with comp(A) & comp(B)
    /// - comp(A&B) with comp(A) | comp(B)
    /// - comp(epsilon) with epsilon All+
    /// - comp(All) with none
    /// - comp(Any) with (epsilon|Any+)
    /// - comp(av) = epsilon | (comp a . All) | (a . comp v) where a is the first character of the word and v the rest
    ///
    /// Additionally, if `fold_ranges` is set to true, also removes complements from range operations as follows
    ///
    /// - replaces comp([l..u]) with [0..(l-1)] | [(u+1)..max]
    /// - replaces comp(a) with [0..(a-1)] | [(a+1)..max]
    ///
    /// Fails to eliminate complement operations in all other cases.
    pub fn apply(
        &mut self,
        re: &Regex,
        builder: &mut ReBuilder,
        fold_ranges: bool,
    ) -> Option<Regex> {
        if let Some(cc) = self.cache.get(re) {
            return Some(cc.clone());
        }

        let result = if !re.contains_complement() {
            re.clone()
        } else {
            match re.op() {
                ReOp::Comp(comped) => match comped.op() {
                    ReOp::Literal(w) => self.comp_word(w.clone(), builder, fold_ranges),
                    ReOp::None => builder.all(),
                    ReOp::All => builder.none(),
                    ReOp::Any => {
                        let anyplus = builder.plus(builder.allchar());
                        builder.union(smallvec![builder.epsilon(), anyplus])
                    }
                    ReOp::Union(rs) => self.comp_union(rs.to_vec(), builder, fold_ranges)?,
                    ReOp::Inter(rs) => self.comp_inter(rs.to_vec(), builder, fold_ranges)?,
                    ReOp::Opt(r) => {
                        // Comp(Opt(A)) = Comp(A | epsilon) = Comp(A) & Comp(epsilon)

                        let comp_r = self.apply(r, builder, fold_ranges)?;
                        let comp_epsilon = self.comp_empty_word(builder);
                        builder.inter(smallvec![comp_r, comp_epsilon])
                    }
                    ReOp::Range(r) => self.comp_range(*r, builder),
                    ReOp::Comp(r) => r.clone(), // double negation
                    ReOp::Diff(r1, r2) => {
                        //comp(a-b) = comp(a & comp(b)) = comp(a) | b
                        let lhs = self.apply(r1, builder, fold_ranges)?;
                        let rhs = self.apply(r2, builder, fold_ranges)?;
                        builder.union(smallvec![lhs, rhs])
                    }
                    _ => unimplemented!("Unsupported complement operation: {}", comped),
                },
                ReOp::Diff(r1, r2) => {
                    self.rewrite_diff(r1.clone(), r2.clone(), builder, fold_ranges)?
                }
                ReOp::Concat(rs) => {
                    let rs = rs
                        .iter()
                        .map(|r| self.apply(r, builder, fold_ranges))
                        .collect::<Option<_>>()?;
                    builder.concat(rs)
                }
                ReOp::Union(rs) => {
                    let rs = rs
                        .iter()
                        .map(|r| self.apply(r, builder, fold_ranges))
                        .collect::<Option<_>>()?;
                    builder.union(rs)
                }
                ReOp::Inter(rs) => {
                    let rs = rs
                        .iter()
                        .map(|r| self.apply(r, builder, fold_ranges))
                        .collect::<Option<_>>()?;
                    builder.inter(rs)
                }
                ReOp::Star(r) => {
                    let rr = self.apply(r, builder, fold_ranges)?;
                    builder.star(rr)
                }
                ReOp::Plus(r) => {
                    let rr = self.apply(r, builder, fold_ranges)?;
                    builder.plus(rr)
                }
                ReOp::Opt(r) => {
                    let rr = self.apply(r, builder, fold_ranges)?;
                    builder.opt(rr)
                }
                ReOp::Pow(r, e) => {
                    let rr = self.apply(r, builder, fold_ranges)?;
                    builder.pow(rr, *e)
                }
                ReOp::Loop(r, l, u) => {
                    let rr = self.apply(r, builder, fold_ranges)?;
                    builder.loop_(rr, *l, *u)
                }
                _ => re.clone(),
            }
        };
        self.cache.insert(re.clone(), result.clone());
        Some(result)
    }

    // r1 - r2 => r1 & ~r2
    fn rewrite_diff(
        &mut self,
        r1: Regex,
        r2: Regex,
        builder: &mut ReBuilder,
        fold_ranges: bool,
    ) -> Option<Regex> {
        let r2comp = builder.comp(r2.clone());
        let r = builder.inter(smallvec![r1.clone(), r2comp]);
        self.apply(&r, builder, fold_ranges)
    }

    /// Comp(A|B) = Comp(A) & Comp(B)
    fn comp_union(
        &mut self,
        rs: Vec<Regex>,
        builder: &mut ReBuilder,
        fold_ranges: bool,
    ) -> Option<Regex> {
        let rs = rs.into_iter().map(|r| builder.comp(r)).collect();
        let as_inter = builder.inter(rs);
        self.apply(&as_inter, builder, fold_ranges)
    }

    /// Comp(A&B) = Comp(A) | Comp(B)
    fn comp_inter(
        &mut self,
        rs: Vec<Regex>,
        builder: &mut ReBuilder,
        fold_ranges: bool,
    ) -> Option<Regex> {
        let rs = rs.into_iter().map(|r| builder.comp(r)).collect();
        let as_union = builder.union(rs);
        self.apply(&as_union, builder, fold_ranges)
    }

    fn comp_empty_word(&self, builder: &mut ReBuilder) -> Regex {
        builder.plus(builder.allchar())
    }

    fn comp_word(&mut self, w: SmtString, builder: &mut ReBuilder, fold_ranges: bool) -> Regex {
        if w.is_empty() {
            self.comp_empty_word(builder)
        } else if fold_ranges {
            // \epsi | ((comp a). ALL) | (a . (comp v))
            let a = w.first().unwrap();
            let v = w.drop(1);

            let a_comp = self.comp_char(a, builder, fold_ranges);
            let a_comp_all = builder.concat(smallvec![a_comp, builder.all()]);
            let b_comp = self.comp_word(v, builder, fold_ranges);

            let re_a = builder.to_re(a.into());
            let a_bcomp = builder.concat(smallvec![re_a, b_comp]);

            builder.union(smallvec![builder.epsilon(), a_comp_all, a_bcomp])
        } else {
            // comp(a) | (a . comp(v))
            let a = w.first().unwrap();
            let v = w.drop(1);

            let a = builder.to_re(a.into());
            let a_comp = builder.comp(a.clone());
            if v.is_empty() {
                a_comp
            } else {
                let v = self.comp_word(v, builder, fold_ranges);
                let a_v = builder.concat(smallvec![a, v]);
                builder.union(smallvec![a_comp, a_v])
            }
        }
    }

    fn comp_char(&mut self, a: SmtChar, builder: &mut ReBuilder, fold_ranges: bool) -> Regex {
        let r = CharRange::singleton(a);
        if fold_ranges {
            self.comp_range(r, builder)
        } else {
            let range = CharRange::singleton(a);
            let a = builder.range(range);
            builder.comp(a)
        }
    }

    fn comp_range(&mut self, r: CharRange, builder: &mut ReBuilder) -> Regex {
        if let Some(re) = self.range_cache.get(&r) {
            return re.clone();
        }
        if r.is_empty() {
            return builder.allchar();
        }
        let diff_r = CharRange::all().subtract(&r);
        let diff_r = diff_r.into_iter().map(|r| builder.range(r)).collect();
        let union = builder.union(diff_r);
        let opt = builder.opt(union);

        self.range_cache.insert(r, opt.clone());
        opt
    }
}

#[cfg(test)]
mod test {
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use smt_str::{
        alphabet::CharRange,
        re::{ReBuilder, ReOp},
        SmtChar, SmtString,
    };

    use super::ReCompRemover;

    #[test]
    #[ignore = "Using complement transitions instead"]
    fn re_comp_canonicalize_char() {
        let mut comp = ReCompRemover::default();
        let mut builder = ReBuilder::default();

        match comp.comp_char('a'.into(), &mut builder, true).op() {
            ReOp::Union(items) => {
                assert_eq!(items[0], builder.range_from_to(0, (b'a' - 1) as u32));
                assert_eq!(items[1], builder.range_from_to('b', SmtChar::MAX));
            }
            _ => unreachable!(),
        }

        let comped = comp.comp_char(0.into(), &mut builder, true);
        match comped.op() {
            ReOp::Range(r) => {
                assert_eq!(*r, CharRange::all());
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

        if let ReOp::Opt(opts) = comp
            .comp_range(CharRange::new(l as char, u as char), &mut builder)
            .op()
        {
            match opts.op() {
                ReOp::Union(items) => {
                    assert_eq!(items[0], builder.range_from_to(0 as char, (l - 1) as char));
                    assert_eq!(
                        items[1],
                        builder.range_from_to((u + 1) as char, SmtChar::MAX)
                    );
                }
                ReOp::Range(r) => {
                    assert_eq!(l, 0);
                    assert_eq!(r.start(), (u as u32 + 1).into());
                }
                x => panic!("Unexpected {}", x),
            }
        } else {
            unreachable!()
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
        if let ReOp::Any = r.op() {
            TestResult::passed()
        } else {
            panic!("Expected empty range to be represented as AllChar but got {r}",);
        }
    }

    #[test]
    fn re_comp_canonicalize_empty_word() {
        let mut comp = ReCompRemover::default();

        let mut builder = ReBuilder::default();
        let w = SmtString::empty();
        let r = comp.comp_word(w, &mut builder, true);
        assert_eq!(r, builder.plus(builder.allchar()));
    }
}
