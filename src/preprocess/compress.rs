use itertools::Itertools;
use smt_str::{
    alphabet::{partition::AlphabetPartition, Alphabet, CharRange},
    re::{ReBuilder, ReOp, Regex},
    SmtChar,
};

use crate::{
    ast::{Node, NodeKind},
    context::Context,
};

use super::complements::ReCompRemover;

#[derive(Default)]
pub struct RangeCompressor {
    comp_folder: ReCompRemover,
}

impl RangeCompressor {
    pub fn compress(&mut self, node: &Node, ctx: &mut Context) -> Node {
        // Try to get rid of complements first
        let node = self.rewrite_complements(node, ctx, true);
        let partioning = self.partition_alphabet(&node);

        self.compress_ranges(&node, &partioning, ctx)
    }

    /// Tries to remove the complements in regular constraints.
    /// For regex with positive polarity, this also rewrites complements of ranges as unions of ranges, meaning `comp([a-c])` becomes `[smt::min-(a-1)]|[(a+1)-smt::max]`.
    /// This is done to allow for more effective range compression.
    /// In negative polarity, compression is not sound and range complements are left as they are.
    fn rewrite_complements(&mut self, node: &Node, ctx: &mut Context, polarity: bool) -> Node {
        match node.kind() {
            NodeKind::InRe => {
                debug_assert!(node.children().len() == 2);
                if let NodeKind::Regex(regex) = node.children()[1].kind() {
                    match self.comp_folder.apply(regex, ctx.re_builder(), polarity) {
                        Some(re) => {
                            let re_node = ctx.ast().const_regex(re);
                            ctx.ast().create_node(
                                NodeKind::InRe,
                                vec![node.children()[0].clone(), re_node],
                            )
                        }
                        None => node.clone(),
                    }
                } else {
                    unreachable!()
                }
            }
            NodeKind::Not => {
                let kind = node.kind().clone();
                let children = node
                    .children()
                    .iter()
                    .map(|child| self.rewrite_complements(child, ctx, !polarity))
                    .collect();
                ctx.ast().create_node(kind, children)
            }
            _ => {
                let kind = node.kind().clone();
                let children = node
                    .children()
                    .iter()
                    .map(|child| self.rewrite_complements(child, ctx, polarity))
                    .collect();
                ctx.ast().create_node(kind, children)
            }
        }
    }

    pub fn compress_ranges(
        &self,
        node: &Node,
        partitioning: &AlphabetPartition,
        ctx: &mut Context,
    ) -> Node {
        match node.kind() {
            NodeKind::Regex(regex) => {
                let compressed_re = self.compress_re_ranges(regex, partitioning, ctx.re_builder());
                ctx.ast().const_regex(compressed_re)
            }
            // Cannot compress negated regular constraints, so we return the node as is
            // Since the formula is in NNF, this check is sufficient
            NodeKind::Not => node.clone(),
            _ => {
                let mut new_children = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    new_children.push(self.compress_ranges(c, partitioning, ctx));
                }
                ctx.ast().create_node(node.kind().clone(), new_children)
            }
        }
    }

    fn compress_re_ranges(
        &self,
        re: &Regex,
        partitioning: &AlphabetPartition,
        builder: &mut ReBuilder,
    ) -> Regex {
        match re.op() {
            ReOp::Range(r) => {
                let reps = self.find_representative_range(r, partitioning);
                let as_res = reps.iter().map(|r| builder.range(*r)).collect();
                builder.union(as_res)
            }
            ReOp::Concat(rs) | ReOp::Union(rs) | ReOp::Inter(rs) => {
                let compressed_rs = rs
                    .iter()
                    .map(|r| self.compress_re_ranges(r, partitioning, builder))
                    .collect();
                match re.op() {
                    ReOp::Concat(_) => builder.concat(compressed_rs),
                    ReOp::Union(_) => builder.union(compressed_rs),
                    ReOp::Inter(_) => builder.inter(compressed_rs),
                    _ => unreachable!(),
                }
            }
            ReOp::Star(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.star(compressed_r)
            }
            ReOp::Plus(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.plus(compressed_r)
            }
            ReOp::Opt(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.opt(compressed_r)
            }
            ReOp::Comp(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.comp(compressed_r)
            }
            ReOp::Diff(r1, r2) => {
                let compressed_r1 = self.compress_re_ranges(r1, partitioning, builder);
                let compressed_r2 = self.compress_re_ranges(r2, partitioning, builder);
                builder.diff(compressed_r1, compressed_r2)
            }
            ReOp::Pow(r, p) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.pow(compressed_r, *p)
            }
            ReOp::Loop(r, l, u) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.loop_(compressed_r, *l, *u)
            }
            _ => re.clone(),
        }
    }

    fn find_representative_range(
        &self,
        range: &CharRange,
        partitioning: &AlphabetPartition,
    ) -> Vec<CharRange> {
        let mut iter = partitioning.iter().peekable();
        // Advance iterator until start matches
        while let Some(r) = iter.peek() {
            if r.start() == range.start() {
                break;
            }
            iter.next();
        }
        // Take ranges while they are contained in the range
        // The union of these ranges is the range itself
        let ranges_in_part = iter.take_while(|r| r.end() <= range.end());
        // map ranges to representatives char, which simply is the start of the range
        let reps = ranges_in_part.map(|r| r.start());

        // We map back the representatives to ranges because they might be adjacent
        // E.g. if the representatives are {'a', 'c', 'z'} we want to return {['a'- 'c'], ['z']}
        // To compute this, we reuse the alphabet canonicalization
        let mut alph = Alphabet::empty();
        for rep in reps {
            alph.insert_char(rep);
        }
        alph.iter_ranges().collect_vec()
    }

    fn partition_alphabet(&self, node: &Node) -> AlphabetPartition {
        match node.kind() {
            NodeKind::String(s) => self.word_to_partitioning(s.iter().copied()),
            NodeKind::Regex(regex) => self.partition_re_alphabet(regex),
            NodeKind::Literal(_) => unreachable!(),
            _ => {
                let mut res = AlphabetPartition::default();
                for c in node.children() {
                    res = res.refine(&self.partition_alphabet(c));
                }
                res
            }
        }
    }

    fn partition_re_alphabet(&self, re: &Regex) -> AlphabetPartition {
        match re.op() {
            ReOp::Literal(word) => self.word_to_partitioning(word.iter().copied()),
            ReOp::Concat(rs) | ReOp::Union(rs) | ReOp::Inter(rs) => {
                let mut res = AlphabetPartition::default();
                for r in rs {
                    res = res.refine(&self.partition_re_alphabet(r));
                }

                res
            }
            ReOp::Range(r) => {
                let mut res = AlphabetPartition::default();
                res.insert_unchecked(*r);
                res
            }
            ReOp::Diff(regex, regex1) => {
                let mut res = self.partition_re_alphabet(regex);
                res = res.refine(&self.partition_re_alphabet(regex1));
                res
            }
            ReOp::Star(r)
            | ReOp::Plus(r)
            | ReOp::Opt(r)
            | ReOp::Comp(r)
            | ReOp::Pow(r, _)
            | ReOp::Loop(r, _, _) => self.partition_re_alphabet(r),
            _ => AlphabetPartition::default(),
        }
    }

    fn word_to_partitioning(&self, word: impl Iterator<Item = SmtChar>) -> AlphabetPartition {
        let mut res = AlphabetPartition::default();
        for c in word.unique() {
            res.insert_unchecked(CharRange::singleton(c));
        }
        res
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use quickcheck_macros::quickcheck;
    use smallvec::smallvec;
    use smt_str::{alphabet::CharRange, SmtChar};

    use crate::{
        ast::testutils::{parse_equation, parse_pattern},
        context::Context,
        preprocess::compress::RangeCompressor,
    };

    #[test]
    fn partition_pattern() {
        let mut ctx = Context::default();
        let p = parse_pattern("XabYabc", &mut ctx);

        let compressor = RangeCompressor::default();
        let partitioning = compressor.partition_alphabet(&p);

        assert!(partitioning.contains(&CharRange::singleton('a')));
        assert!(partitioning.contains(&CharRange::singleton('b')));
        assert!(partitioning.contains(&CharRange::singleton('c')));
    }

    #[test]
    fn partition_weq() {
        let mut ctx = Context::default();
        let p = parse_equation("XabYabc", "abXcYd", &mut ctx);

        let compressor = RangeCompressor::default();
        let partitioning = compressor.partition_alphabet(&p);

        assert!(partitioning.contains(&CharRange::singleton('a')));
        assert!(partitioning.contains(&CharRange::singleton('b')));
        assert!(partitioning.contains(&CharRange::singleton('c')));
        assert!(partitioning.contains(&CharRange::singleton('d')));
    }

    #[quickcheck]
    fn word_to_partitioning(chars: Vec<SmtChar>) {
        let word = chars.into_iter();

        let compressor = RangeCompressor::default();
        let partitioning = compressor.word_to_partitioning(word.clone());

        let unique_chars = word.unique().collect::<Vec<_>>();
        assert!(partitioning.len() == unique_chars.len());
        for c in unique_chars {
            assert!(partitioning.contains(&CharRange::singleton(c)));
        }
    }

    #[test]
    fn partition_re_union() {
        let mut ctx = Context::default();

        // Can't do overlapping ranges because the builder will unify them
        let re_builder = ctx.re_builder();
        let a_to_c = re_builder.range(CharRange::new('a', 'c'));
        let e_to_f = re_builder.range(CharRange::new('e', 'f'));
        let h_to_z = re_builder.range(CharRange::new('h', 'z'));
        let re = re_builder.union(smallvec![a_to_c, e_to_f, h_to_z]);

        let compressor = RangeCompressor::default();
        let partitioning = compressor.partition_re_alphabet(&re);

        assert!(
            partitioning.contains(&CharRange::new('a', 'c')),
            "{}",
            partitioning
        );
        assert!(partitioning.contains(&CharRange::new('e', 'f')));
        assert!(partitioning.contains(&CharRange::new('h', 'z')));
    }

    #[test]
    fn partition_re_concat() {
        let mut ctx = Context::default();

        // Can't do overlapping ranges because the builder will unify them
        let re_builder = ctx.re_builder();
        let a_to_z = re_builder.range(CharRange::new('a', 'z'));
        let e_to_x = re_builder.range(CharRange::new('e', 'x'));
        let h_to_z = re_builder.range(CharRange::new('h', 'z'));
        let a = re_builder.to_re("a".into());
        let re = re_builder.concat(smallvec![a_to_z, e_to_x, a, h_to_z]);

        let compressor = RangeCompressor::default();
        let partitioning = compressor.partition_re_alphabet(&re);

        assert_eq!(partitioning.len(), 5);
        assert!(partitioning.contains(&CharRange::new('a', 'a')),);
        assert!(partitioning.contains(&CharRange::new('b', 'd')));
        assert!(partitioning.contains(&CharRange::new('e', 'g')));
        assert!(partitioning.contains(&CharRange::new('h', 'x')),);
        assert!(partitioning.contains(&CharRange::new('y', 'z')));
    }
}
