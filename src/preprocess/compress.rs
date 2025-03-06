use itertools::Itertools;
use regulaer::{
    alph::{Alphabet, CharPartitioning, CharRange},
    re::{ReBuilder, RegOp, Regex},
};

use crate::node::{Node, NodeKind, NodeManager};

#[derive(Default)]
pub struct RangeCompressor {}

impl RangeCompressor {
    pub fn compress(&self, node: &Node, mngr: &mut NodeManager) -> Node {
        let partioning = self.partition_alphabet(node);
        let compressed = self.compress_ranges(node, &partioning, mngr);
        compressed
    }

    pub fn compress_ranges(
        &self,
        node: &Node,
        partitioning: &CharPartitioning,
        mngr: &mut NodeManager,
    ) -> Node {
        match node.kind() {
            NodeKind::Regex(regex) => {
                let compressed_re = self.compress_re_ranges(regex, partitioning, mngr.re_builder());
                mngr.const_regex(compressed_re)
            }
            _ => {
                let mut new_children = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    new_children.push(self.compress_ranges(c, partitioning, mngr));
                }
                mngr.create_node(node.kind().clone(), new_children)
            }
        }
    }

    fn compress_re_ranges(
        &self,
        re: &Regex,
        partitioning: &CharPartitioning,
        builder: &mut ReBuilder,
    ) -> Regex {
        match re.op() {
            RegOp::Range(r) => {
                let reps = self.find_representative_range(r, partitioning);
                let as_res = reps
                    .iter()
                    .map(|r| builder.range(r.start(), r.end()))
                    .collect();
                builder.union(as_res)
            }
            RegOp::Concat(rs) | RegOp::Union(rs) | RegOp::Inter(rs) => {
                let compressed_rs = rs
                    .iter()
                    .map(|r| self.compress_re_ranges(r, partitioning, builder))
                    .collect_vec();
                match re.op() {
                    RegOp::Concat(_) => builder.concat(compressed_rs),
                    RegOp::Union(_) => builder.union(compressed_rs),
                    RegOp::Inter(_) => builder.inter(compressed_rs),
                    _ => unreachable!(),
                }
            }
            RegOp::Star(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.star(compressed_r)
            }
            RegOp::Plus(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.plus(compressed_r)
            }
            RegOp::Opt(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.opt(compressed_r)
            }
            RegOp::Comp(r) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.comp(compressed_r)
            }
            RegOp::Diff(r1, r2) => {
                let compressed_r1 = self.compress_re_ranges(r1, partitioning, builder);
                let compressed_r2 = self.compress_re_ranges(r2, partitioning, builder);
                builder.diff(compressed_r1, compressed_r2)
            }
            RegOp::Pow(r, p) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.pow(compressed_r, *p)
            }
            RegOp::Loop(r, l, u) => {
                let compressed_r = self.compress_re_ranges(r, partitioning, builder);
                builder.loop_(compressed_r, *l, *u)
            }
            _ => re.clone(),
        }
    }

    fn find_representative_range(
        &self,
        range: &CharRange,
        partitioning: &CharPartitioning,
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
        alph.canonicalize();
        alph.iter_ranges().cloned().collect_vec()
    }

    fn partition_alphabet(&self, node: &Node) -> CharPartitioning {
        match node.kind() {
            NodeKind::String(s) => self.word_to_partitioning(s.chars()),
            NodeKind::Regex(regex) => self.partition_re_alphabet(regex),
            NodeKind::Literal(_) => unreachable!(),
            _ => {
                let mut res = CharPartitioning::default();
                for c in node.children() {
                    res = res.refine(&self.partition_alphabet(c));
                }
                res
            }
        }
    }

    fn partition_re_alphabet(&self, re: &Regex) -> CharPartitioning {
        match re.op() {
            RegOp::Const(word) => self.word_to_partitioning(word.iter()),
            RegOp::Concat(rs) | RegOp::Union(rs) | RegOp::Inter(rs) => {
                let mut res = CharPartitioning::default();
                for r in rs {
                    res = res.refine(&self.partition_re_alphabet(r));
                }

                res
            }
            RegOp::Range(r) => {
                let mut res = CharPartitioning::default();
                res.insert_unchecked(*r);
                res
            }
            RegOp::Diff(regex, regex1) => {
                let mut res = self.partition_re_alphabet(regex);
                res = res.refine(&self.partition_re_alphabet(regex1));
                res
            }
            RegOp::Star(r)
            | RegOp::Plus(r)
            | RegOp::Opt(r)
            | RegOp::Comp(r)
            | RegOp::Pow(r, _)
            | RegOp::Loop(r, _, _) => self.partition_re_alphabet(r),
            _ => CharPartitioning::default(),
        }
    }

    fn word_to_partitioning(&self, word: impl Iterator<Item = char>) -> CharPartitioning {
        let mut res = CharPartitioning::default();
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
    use regulaer::{alph::CharRange, parse::parse_rust};

    use crate::node::{
        testutils::{parse_equation, parse_pattern},
        NodeManager,
    };

    #[test]
    fn partition_pattern() {
        let mut mngr = NodeManager::default();
        let p = parse_pattern("XabYabc", &mut mngr);

        let compressor = super::RangeCompressor {};
        let partitioning = compressor.partition_alphabet(&p);

        assert!(partitioning.contains(&CharRange::singleton('a')));
        assert!(partitioning.contains(&CharRange::singleton('b')));
        assert!(partitioning.contains(&CharRange::singleton('c')));
    }

    #[test]
    fn partition_weq() {
        let mut mngr = NodeManager::default();
        let p = parse_equation("XabYabc", "abXcYd", &mut mngr);

        let compressor = super::RangeCompressor {};
        let partitioning = compressor.partition_alphabet(&p);

        assert!(partitioning.contains(&CharRange::singleton('a')));
        assert!(partitioning.contains(&CharRange::singleton('b')));
        assert!(partitioning.contains(&CharRange::singleton('c')));
        assert!(partitioning.contains(&CharRange::singleton('d')));
    }

    #[quickcheck]
    fn word_to_partitioning(chars: Vec<char>) {
        let word = chars.into_iter().filter(|c| c.is_alphanumeric());

        let compressor = super::RangeCompressor {};
        let partitioning = compressor.word_to_partitioning(word.clone());

        let unique_chars = word.unique().collect::<Vec<_>>();
        assert!(partitioning.len() == unique_chars.len());
        for c in unique_chars {
            assert!(partitioning.contains(&CharRange::singleton(c)));
        }
    }

    #[test]
    fn partition_re_union() {
        let mut mngr = NodeManager::default();

        // Can't do overlapping ranges because the builder will unify them
        let re = parse_rust(r#"[a-c]|[e-f]|[h-z]"#, mngr.re_builder(), true).unwrap();

        println!("Parsed: {}", re);

        let compressor = super::RangeCompressor {};
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
        let mut mngr = NodeManager::default();

        // Can't do overlapping ranges because the builder will unify them
        let re = parse_rust(r#"[a-z][e-x]a[h-z]"#, mngr.re_builder(), true).unwrap();

        println!("Parsed: {}", re);

        let compressor = super::RangeCompressor {};
        let partitioning = compressor.partition_re_alphabet(&re);

        assert_eq!(partitioning.len(), 5);
        assert!(partitioning.contains(&CharRange::new('a', 'a')),);
        assert!(partitioning.contains(&CharRange::new('b', 'd')));
        assert!(partitioning.contains(&CharRange::new('e', 'g')));
        assert!(partitioning.contains(&CharRange::new('h', 'x')),);
        assert!(partitioning.contains(&CharRange::new('y', 'z')));
    }
}
