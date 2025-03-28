use std::{fmt::Display, rc::Rc};

use indexmap::IndexMap;
use rustsat::clause;
use rustsat::solvers::Solve;
use rustsat_cadical::CaDiCaL;
use smt_str::SmtString;

use crate::{
    domain::Domain,
    encode::{domain::DomainEncoding, EncodingResult, LAMBDA},
    node::{
        canonical::{Pattern, Symbol},
        Variable,
    },
    sat::{nlit, plit, pvar, PVar},
};

use super::word::WordEncoding;

/// A segment of a pattern, i.e., a string constant or a variable.
/// A factor of a pattern is called a *segment* iff
/// - it is a variable, or
/// - it is a string constant that cannot be extended to the left or right (i.e., it is not a prefix or suffix of another constant factor).
#[derive(Clone, Debug, PartialEq, Eq)]
enum PatternSegment {
    /// A string variable
    Variable(Rc<Variable>),
    /// A string constant
    Word(SmtString),
}

impl Display for PatternSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternSegment::Variable(v) => write!(f, "{}", v),
            PatternSegment::Word(w) => write!(f, "{}", w),
        }
    }
}

/// A pattern that is split into [segments](PatternSegment).
#[derive(Clone, Debug)]
struct SegmentedPattern {
    segments: Vec<PatternSegment>,
}

impl SegmentedPattern {
    /// Creates a new segmented pattern from the given pattern.
    fn new(pattern: Pattern) -> Self {
        let mut segments = Vec::new();
        let mut w = SmtString::empty();
        for pos in pattern.symbols() {
            match pos {
                Symbol::Constant(c) => {
                    w.push(*c);
                }
                Symbol::Variable(v) => {
                    if !w.is_empty() {
                        segments.push(PatternSegment::Word(w.clone()));
                        w.clear();
                    }
                    segments.push(PatternSegment::Variable(v.clone()));
                }
            }
        }
        if !w.is_empty() {
            segments.push(PatternSegment::Word(w));
        }
        if segments.is_empty() {
            segments.push(PatternSegment::Word(SmtString::empty()));
        }
        Self { segments }
    }

    /// The number of segments in the pattern
    fn length(&self) -> usize {
        self.segments.len()
    }

    /// Returns the segment at position i, panics if i is out of bounds.
    fn get(&self, i: usize) -> &PatternSegment {
        &self.segments[i]
    }

    /// Returns the number of constant prior to the i-th segment, not including the i-th segment.
    /// This equals to the length of the prefix preceding the i-th segment when all variables are mapped to the empty word.
    /// This is equivalent to the earliest start position of the i-th segment.
    fn consts_before(&self, i: usize) -> usize {
        let mut pos = 0;
        for j in 0..i {
            match self.get(j) {
                PatternSegment::Variable(_v) => pos += 0, /*  {
                pos += bounds.get_lower(&v.len_var().unwrap()).unwrap_or(0) as usize
                }*/
                PatternSegment::Word(w) => pos += w.len(),
            }
        }
        pos
    }

    /// Returns the number of constant after the i-th segment, not including the i-th segment.
    /// This equals to the length of the suffix following the i-th segment when all variables are mapped to the empty word.
    /// This is equivalent to the latest end position of the i-th segment.
    fn consts_after(&self, i: usize) -> usize {
        let mut f = 0;

        for j in i + 1..self.length() {
            match self.get(j) {
                PatternSegment::Variable(_v) => (),
                PatternSegment::Word(w) => f += w.len(),
            }
        }
        f
    }
}

impl Display for SegmentedPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for seg in self.segments.iter() {
            write!(f, "{}", seg)?;
        }
        Ok(())
    }
}

pub(super) struct PatternMatchingEncoder {
    pattern: SegmentedPattern,
    /// The encoding of the start position of each segment in the pattern.
    /// start_pos[(i, j)] is a Boolean variable that is true if and only if the i-th segments of the pattern starts at position j.
    ///
    /// If the pattern as n segments, then this map has entries for n+1 segements.
    /// The last segment is used to define the end of the pattern and is not actually part of the pattern.
    start_pos: IndexMap<(usize, usize), PVar>,

    /// The length of the word to be matched.
    len: Option<usize>,
    /// The bounds of the variables in the pattern used to encode the matching.
    bounds: Domain,

    /// A Boolean variable that is added as an assumption to the SAT solver.
    /// The negation of this variable is added as an assumption.
    /// The selector is valid for only one call to `encode`.
    selector: Option<PVar>,

    /// A cache for the matching of variables to the word.
    /// The value for key (v, p, l) is a Boolean variable that is true if and only if the variable v matches the word at position p with length l.
    match_cache: IndexMap<(Rc<Variable>, usize, usize), PVar>,
}

impl PatternMatchingEncoder {
    pub fn new(pattern: Pattern) -> Self {
        let pattern = SegmentedPattern::new(pattern);
        Self {
            pattern,
            start_pos: IndexMap::new(),
            len: None,
            bounds: Domain::empty(),
            selector: None,
            match_cache: IndexMap::new(),
        }
    }

    /// Encodes the matching of the pattern to the word, represented by the given word encoding.
    pub fn encode(
        &mut self,
        word: &WordEncoding,
        bounds: &Domain,
        dom: &DomainEncoding,
    ) -> EncodingResult {
        assert!(
            self.len.unwrap_or(0) <= word.len(),
            "Word length cannot shrink"
        );

        self.selector = Some(pvar());

        self.init_start_positions(word);
        let mut res = EncodingResult::empty();
        self.encode_pattern_start(&mut res);
        self.encode_pattern_end(word, &mut res);
        self.disable_early_starts(word, &mut res);
        self.encode_match(word, bounds, dom, &mut res);

        // add the selector as an assumption
        res.add_assumption(plit(self.selector.unwrap()));

        self.bounds = bounds.clone();
        self.len = Some(word.len());
        res
    }

    fn init_start_positions(&mut self, word: &WordEncoding) {
        let wlen = word.len(); // the length of the word to be matched
        let segs = self.pattern.length(); // the number of segments in the pattern

        // Initialize the start position encoding for all segments and positions
        for s in 0..segs + 1 {
            for len in self.len.unwrap_or(0)..wlen {
                let p = pvar();
                self.start_pos.insert((s, len), p);
            }
        }
    }

    /// Encode that the first segment starts at position 0
    fn encode_pattern_start(&self, res: &mut EncodingResult) {
        if self.len.is_none() {
            let p = self.starts_at(0, 0);
            res.add_clause(clause![plit(p)]);
        }
    }

    /// Encode the end of the pattern by asserting that from the start position of the end segment, the word is empty
    fn encode_pattern_end(&self, word: &WordEncoding, res: &mut EncodingResult) {
        let wlen = word.len(); // the length of the word to be matched
        let end_seg = self.pattern.length(); // the number of segments in the pattern
        for len in self.len.unwrap_or(0)..wlen {
            let p = self.starts_at(end_seg, len);
            // end segment starts at position len -> word[len] = lambda
            res.add_clause(clause![nlit(p), plit(word.at(len, LAMBDA))]);
        }
    }

    /// Disables start positions pos for all segments i if i cannot start at position pos.
    fn disable_early_starts(&self, word: &WordEncoding, res: &mut EncodingResult) {
        let wlen = word.len(); // the length of the word to be matched
        for seg in 0..self.pattern.length() {
            for pos in self.len.unwrap_or(0)..wlen {
                if pos < self.pattern.consts_before(seg) {
                    // The segment cannot start here, disable this position using assumption: !start_pos[i][pos]
                    let starts_here = self.starts_at(seg, pos);
                    res.add_clause(clause![nlit(starts_here)]);
                }
            }
        }
    }

    /// For all segments i, start positions `pos`, and lengths `len`,
    /// encodes that if the i-th segment starts at position `pos` and has lenght `len` then
    /// - segment i+1 starts at position `len`+l
    /// - the word at positions `len`..`len`+l is equal to the segment i+1
    fn encode_match(
        &mut self,
        word: &WordEncoding,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        res: &mut EncodingResult,
    ) {
        let segs = self.pattern.length(); // the number of segments in the pattern

        for seg in 0..segs {
            match self.pattern.get(seg).clone() {
                PatternSegment::Variable(v) => {
                    let vbound =
                        dom.get_string(&v)
                            .and_then(|i| i.upper_finite())
                            .expect("No upper bound for variable") as usize;
                    let last_vbound = self
                        .bounds
                        .get_string(&v)
                        .and_then(|i| i.upper_finite())
                        .unwrap_or(0) as usize;
                    self.encode_match_variable(seg, &v, vbound, last_vbound, word, dom_enc, res)
                }
                PatternSegment::Word(w) => self.encode_match_const(seg, &w, word, res),
            }
        }
    }

    /// Encodes matching for segment i in case it is a constant word |w|
    fn encode_match_const(
        &self,
        i: usize,
        w: &SmtString,
        word: &WordEncoding,
        res: &mut EncodingResult,
    ) {
        debug_assert_eq!(*self.pattern.get(i), PatternSegment::Word(w.clone()));

        // We need to consider all start positions from (last length) - (|w| + const_after(i)) to the end of the word
        // subtracting (|w| + const_after(i)) is required because these position where unusable in the last iteration, as they would exceed the word length (and were disabled by assumptions)
        // In this iteration, we need to consider them, as the word length might have increased.
        let earliest = self
            .len
            .unwrap_or(0)
            .saturating_sub(w.len())
            .saturating_sub(self.pattern.consts_after(i));
        // if this is smaller than the sum of constant prior to this segment, we can skip those positions
        let earliest = earliest.max(self.pattern.consts_before(i));

        for pos in earliest..word.len() {
            let starts_here = self.starts_at(i, pos);
            // check if the segment can start here
            if pos + w.len() < word.len().saturating_sub(self.pattern.consts_after(i)) {
                // Encode that the next w.len() positions in the solution word  are equal to w
                for (k, c) in w.iter().enumerate() {
                    let cand_var = word.at(pos + k, *c);
                    res.add_clause(clause![nlit(starts_here), plit(cand_var)]);
                }
                // Encode that i+1 starts at pos + w.len()
                let succ_start = self.starts_at(i + 1, pos + w.len());
                res.add_clause(clause![nlit(starts_here), plit(succ_start)]);
            } else {
                // Disable this position using assumption: !start_pos[i][pos]
                res.add_assumption(nlit(starts_here));
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_match_variable(
        &mut self,
        i: usize,
        v: &Rc<Variable>,
        vbound: usize,
        last_vbound: usize,
        word: &WordEncoding,
        dom: &DomainEncoding,
        res: &mut EncodingResult,
    ) {
        debug_assert_eq!(*self.pattern.get(i), PatternSegment::Variable(v.clone()));

        let last_len = self
            .len
            .unwrap_or(0)
            .saturating_sub(self.pattern.consts_after(i));

        let earlist = self.pattern.consts_before(i);

        // TODO: for the first segment it is sufficient to consider the first position!!
        for pos in earlist..word.len() {
            for len in 0..=vbound {
                // Check if this was encoded in the last iteration
                if pos < last_len && len < last_vbound && pos + len < last_len {
                    continue;
                }

                let has_length = dom
                    .string()
                    .get_len(v, len)
                    .unwrap_or_else(|| panic!("No length {} for variable {}", len, v));
                let starts_at = self.starts_at(i, pos);

                let latest = word.len().saturating_sub(self.pattern.consts_after(i));
                if pos + len < latest {
                    // encode that var = w[pos..pos+len].
                    // this is encoded inducively:
                    // - length = 1: var = w[0]
                    // - length = l: (length = l-1) AND var[l-1] = w[l-1]
                    // The encoding for a specific length and position is 'cached' by using a Boolean variable that is equivalent to the matching of the variable to the word at the given position and length.
                    // For length 0 we do not need to encode anything, as the variable is empty.
                    if len == 1 {
                        let m_var: u32 = pvar();
                        self.match_cache.insert((v.clone(), pos, len), m_var);
                        for c in dom.alphabet().iter() {
                            let cand_c = word.at(pos, c);
                            let sub_c = dom.string().get_sub(v, 0, c).unwrap();
                            res.add_clause(clause![nlit(m_var), nlit(cand_c), plit(sub_c)]);
                            res.add_clause(clause![nlit(m_var), plit(cand_c), nlit(sub_c)]);
                        }
                        res.add_clause(clause![nlit(starts_at), nlit(has_length), plit(m_var)]);
                    } else if len > 1 {
                        let m_var = pvar();
                        // The Boolean variable equivalent to the matching of the variable to the word at the given position and length-1.
                        let pred_m_var = *self
                            .match_cache
                            .get(&(v.clone(), pos, len - 1))
                            .unwrap_or_else(|| {
                                panic!(
                                    "No match variable for {} at {} with length {}",
                                    v,
                                    pos,
                                    len - 1
                                )
                            });
                        res.add_clause(clause![nlit(m_var), plit(pred_m_var)]);
                        self.match_cache.insert((v.clone(), pos, len), m_var);

                        /* THIS CACHING IS NOT WORKING IF WE HAVE INEQUALITY: The caching assumes we match against the same word, but in case of inequality, we match against two different words, and the cache is invalid.
                        // Cache this with variable
                        I.e., match(x[l-1], cand[p+l-1]) -> EX c. such that they match
                        let mv = match self.var_cand_match_cache.get(&(
                            x.clone(),
                            l - 1,
                            p + (l - 1),
                        )) {
                            Some(mv) => *mv,
                            None => {
                                let mv = pvar();
                                for c in dom.alphabet().iter() {
                                    let cand_c = word.char_at(p + (l - 1), c);
                                    let sub_c = subs.get_sub(x, l - 1, c).unwrap();
                                    clauses.push(vec![
                                        nlit(mv),
                                        nlit(cand_c),
                                        plit(sub_c),
                                    ]);
                                    clauses.push(vec![
                                        nlit(mv),
                                        plit(cand_c),
                                        nlit(sub_c),
                                    ]);
                                }
                                self.var_cand_match_cache
                                    .insert((x.clone(), l - 1, p + (l - 1)), mv);
                                mv
                            }
                        };
                        clauses.push(vec![nlit(m_var), plit(mv)]);*/

                        for c in dom.alphabet().iter() {
                            let cand_c = word.at(pos + (len - 1), c);
                            let sub_c = dom.string().get_sub(v, len - 1, c).unwrap();
                            res.add_clause(clause![nlit(m_var), nlit(cand_c), plit(sub_c)]);
                            res.add_clause(clause![nlit(m_var), plit(cand_c), nlit(sub_c)]);
                        }

                        res.add_clause(clause![nlit(starts_at), nlit(has_length), plit(m_var)]);
                    }

                    // encode that i+1 starts at pos + len
                    let succ_start = self.starts_at(i + 1, pos + len);
                    res.add_clause(clause![nlit(starts_at), nlit(has_length), plit(succ_start)]);
                } else {
                    // Disable this position-length pair using assumption
                    let selector = self.selector.unwrap();
                    // selector -> !start_pos[i][pos] || !has_length
                    res.add_clause(clause![nlit(selector), nlit(starts_at), nlit(has_length)]);
                }
            }
        }
    }

    /// Returns the Boolean variable representing whether the i-th segment of the pattern starts at position j.
    ///
    /// # Arguments
    /// - `seg`: The index of the segment in the pattern.
    /// - `pos`: The position in the word.
    ///
    /// # Panics
    /// Panics if the encoding for the start position of the segment at the given position does not exist.
    /// This is the case if `seg` is out of bounds or `pos` is out of bounds.
    fn starts_at(&self, seg: usize, pos: usize) -> PVar {
        self.start_pos.get(&(seg, pos)).copied().unwrap_or_else(|| {
            panic!(
                "No encoding for start position of segment {} at {}",
                seg, pos
            )
        })
    }

    #[allow(dead_code)]
    pub(super) fn print_start_positions(&self, solver: &mut CaDiCaL) {
        let sol = solver.full_solution().unwrap();
        for (i, seg) in self.pattern.segments.iter().enumerate() {
            let mut found = false;
            for pos in 0..self.len.unwrap_or(0) {
                let p = self.starts_at(i, pos);
                if sol.lit_value(plit(p)).to_bool_with_def(false) {
                    println!("Segment {} ({}) starts at position {}", seg, i, pos);
                    found = true;
                }
            }
            if !found {
                panic!("Segment {} ({}) does not start", seg, i);
            }
        }
    }
}
