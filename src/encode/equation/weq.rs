use std::cmp::{max, min};

use std::fmt::Display;
use std::time::Instant;

use crate::bounds::Bounds;

use crate::context::Variable;
use crate::encode::card::{exactly_one, IncrementalALO};
use crate::encode::domain::DomainEncoding;
use crate::encode::{EncodingError, EncodingResult, FilledPattern, LiteralEncoder, LAMBDA};

use crate::ir::{Pattern, Symbol, WordEquation};
use crate::sat::{nlit, plit, pvar, Cnf, PVar};

use indexmap::{indexset, IndexMap};

/// A segment of a pattern, i.e., a string constant or a variable.
/// A factor of a pattern is called a *segment* iff
/// - it is a variable, or
/// - it is a string constant that cannot be extended to the left or right (i.e., it is not a prefix or suffix of another constant factor).
#[derive(Clone, Debug, PartialEq, Eq)]
enum PatternSegment {
    /// A string variable
    Variable(Variable),
    /// A string constant
    Word(Vec<char>),
}

/// A pattern that is split into [segments](PatternSegment).
#[derive(Clone, Debug)]
struct SegmentedPattern {
    segments: Vec<PatternSegment>,
}

impl SegmentedPattern {
    /// Creates a new segmented pattern from the given pattern.
    fn new(pattern: &Pattern) -> Self {
        let mut segments = Vec::new();
        let mut w = vec![];
        for pos in pattern.symbols() {
            match pos {
                Symbol::Constant(c) => {
                    w.push(*c);
                }
                Symbol::Variable(v) => {
                    if !w.is_empty() {
                        segments.push(PatternSegment::Word(w));
                        w = vec![]
                    }
                    segments.push(PatternSegment::Variable(v.clone()));
                }
            }
        }
        if !w.is_empty() {
            segments.push(PatternSegment::Word(w));
        }
        if segments.is_empty() {
            segments.push(PatternSegment::Word(vec![]));
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

    /// Returns the minimal length of the suffix of the pattern starting at segment before position i (not including segment i).
    /// The minimal prefix length is the sum of the lower bounds of all variables and length of all constants in the prefix.
    fn prefix_min_len(&self, i: usize, _bounds: &Bounds) -> usize {
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

    /// Returns the minimal length of the suffix of the pattern starting at segment after position i (not including segment i).
    /// The minimal suffix length is the sum of the lower bounds of all variables and length of all constants in the suffix.
    // TODO: How does this affect the encoding if the LOWER bound of a variable changes? Is this why we need to keep lower bounds at 0 to avoid soundness errors?
    fn suffix_min_len(&self, i: usize, _bounds: &Bounds) -> usize {
        let mut f = 0;

        for j in i + 1..self.length() {
            match self.get(j) {
                PatternSegment::Variable(_v) => f += 0,
                PatternSegment::Word(w) => f += w.len(),
            }
        }
        f
    }

    fn iter(&self) -> impl Iterator<Item = &PatternSegment> {
        self.segments.iter()
    }
}

/// A side of the equation, i.e., the LHS or RHS.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum EqSide {
    Lhs,
    Rhs,
}

/// Encoder for constant words with an upper bound.
/// Uses an encoding that is incremental, i.e., the encoding for a bound `n` is a subset of the encoding for a bound `m` with `n < m`.
struct WordEncoder {
    /// The last bound that was used, is `0` prior to the first round.
    last_bound: usize,

    /// The Boolean variables that encode the word
    /// Maps pairs of positions and characters to a propositional variable that is true if the character is at the position.
    encoding: IndexMap<(usize, char), PVar>,
}

impl WordEncoder {
    /// Creates a new word encoding.
    fn new() -> Self {
        Self {
            last_bound: 0,
            encoding: IndexMap::new(),
        }
    }

    /// Returns the Boolean variable that is true if the character is at the position in the candidate solution word.
    pub fn char_at(&self, pos: usize, c: char) -> PVar {
        debug_assert!(
            self.encoding.contains_key(&(pos, c)),
            "No candidate at position {} with character {}",
            pos,
            c
        );
        self.encoding[&(pos, c)]
    }

    /// Sets the Boolean variable that is true if the character is at the position in the candidate solution word.
    /// Panics if the variable was already set.
    fn define_char_at(&mut self, pos: usize, c: char, var: PVar) {
        let res = self.encoding.insert((pos, c), var);
        assert!(res.is_none());
    }

    /// Encodes the possible candidates for the solution word up to bound `self.bound`.
    pub fn encode(&mut self, dom: &DomainEncoding, bound: usize) -> EncodingResult {
        assert!(bound >= self.last_bound, "Bound cannot shrink");
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound;
        for pos in last_bound..bound {
            let mut p_choices = vec![];
            for c in dom.alphabet().iter() {
                let v = pvar();
                p_choices.push(v);
                self.define_char_at(pos, c, v);
            }
            let v_lambda = pvar();
            p_choices.push(v_lambda);
            self.define_char_at(pos, LAMBDA, v_lambda);

            let cnf = exactly_one(&p_choices);
            res.extend(EncodingResult::cnf(cnf));

            // Symmetry breaking: If a position is lambda, then only lambda may follow
            if pos > 0 {
                let last_lambda = self.char_at(pos - 1, LAMBDA);
                res.extend(EncodingResult::cnf(vec![vec![
                    nlit(last_lambda),
                    plit(v_lambda),
                ]]));
            }
        }
        self.last_bound = bound;
        res
    }
}

/// Encodes a solution for a word (in-)equation.
enum SolutionWord {
    Equality(WordEncoder),
    Inequality(WordEncoder, WordEncoder),
}

impl SolutionWord {
    fn encode(&mut self, bound: usize, dom: &DomainEncoding) -> EncodingResult {
        match self {
            SolutionWord::Equality(w) => w.encode(dom, bound),
            SolutionWord::Inequality(w1, w2) => {
                let mut res = w1.encode(dom, bound);
                res.extend(w2.encode(dom, bound));
                res
            }
        }
    }

    fn lhs_encoder(&self) -> &WordEncoder {
        match self {
            SolutionWord::Equality(w) => w,
            SolutionWord::Inequality(w, _) => w,
        }
    }

    fn is_equality(&self) -> bool {
        match self {
            SolutionWord::Equality(_) => true,
            SolutionWord::Inequality(_, _) => false,
        }
    }

    fn rhs_encoder(&self) -> &WordEncoder {
        match self {
            SolutionWord::Equality(w) => w,
            SolutionWord::Inequality(_, w) => w,
        }
    }

    fn encoder_for(&self, side: &EqSide) -> &WordEncoder {
        match side {
            EqSide::Lhs => self.lhs_encoder(),
            EqSide::Rhs => self.rhs_encoder(),
        }
    }
}

/// The alignment-based encoder for word equations.
/// This encoder is based on the following idea that segments of the LHS and RHS need to be aligned with a solution word.
pub struct WordEquationEncoder {
    /// The original word equation
    equation: WordEquation,
    pol: bool,

    /// The type of the equation, i.e., equality or inequality.
    /// If the equation is an inequality, then the first word encoding is for the LHS and the second for the RHS.
    /// If the equation is an equality, then one word encoding (= the solution word) is used for both sides.
    candidates: SolutionWord,

    /// Upper bound for the solution word, is 0 prior to first round.
    bound: usize,

    /// The last bound that was used, is `None` prior to the first round.
    last_bound: Option<usize>,

    /// A Boolean variable that is added as an assumption to the SAT solver for the current upper bound.
    /// The negation of this variable is added as an assumption at the next upper bound.
    bound_selector: Option<PVar>,

    /// The variable bounds used in the last round.
    /// Is `None` in the first round.
    last_var_bounds: Option<Bounds>,

    /// Counts the rounds, is 0 prior to the first round and is incremented each call to `encode`.
    round: usize,

    /// The segments of the LHS of the equation.
    segments_lsh: SegmentedPattern,
    /// The segments of the RHS of the equation.
    segments_rhs: SegmentedPattern,

    /// Boolean variables that are true if the segment of the LHS starts at the position.
    starts_lhs: IndexMap<(usize, usize), PVar>,
    /// Boolean variables that are true if the segment of the RHS starts at the position.
    starts_rhs: IndexMap<(usize, usize), PVar>,

    /// Maps each segment index to and incremental at-most-one encoder that is used to encode the possible start positions of the segment.
    //segs_starts_amo: IndexMap<(EqSide, usize), IncrementalAMO>,

    /// The variable-solution matching variables.
    var_matches: IndexMap<(Variable, usize, usize), PVar>,

    mismatch_alo: IncrementalALO,
}

impl WordEquationEncoder {
    pub fn new(equation: WordEquation, pol: bool) -> Self {
        let lhs_segs = SegmentedPattern::new(&equation.lhs());
        let rhs_segs = SegmentedPattern::new(&equation.rhs());

        let eq_type = if pol {
            SolutionWord::Equality(WordEncoder::new())
        } else {
            SolutionWord::Inequality(WordEncoder::new(), WordEncoder::new())
        };

        Self {
            equation,
            bound_selector: None,
            round: 0,
            bound: 0,
            pol,
            candidates: eq_type,
            last_bound: None,
            last_var_bounds: None,
            starts_lhs: IndexMap::new(),
            starts_rhs: IndexMap::new(),
            //segs_starts_amo: IndexMap::new(),
            segments_lsh: lhs_segs,
            segments_rhs: rhs_segs,

            mismatch_alo: IncrementalALO::new(),
            var_matches: IndexMap::new(),
        }
    }

    fn segments(&self, side: &EqSide) -> &SegmentedPattern {
        match side {
            EqSide::Lhs => &self.segments_lsh,
            EqSide::Rhs => &self.segments_rhs,
        }
    }

    /// Returns the Boolean variable that is true if the segment of the given side starts at the given position.
    fn start_position(&self, seg: usize, pos: usize, side: &EqSide) -> PVar {
        match side {
            EqSide::Lhs => self.starts_lhs[&(seg, pos)],
            EqSide::Rhs => self.starts_rhs[&(seg, pos)],
        }
    }

    /// Sets the Boolean variable that is true if the segment of the given side starts at the given position.
    /// Panics if the variable was already set.
    fn set_start_position(&mut self, seg: usize, pos: usize, side: &EqSide, var: PVar) {
        let res = match side {
            EqSide::Lhs => self.starts_lhs.insert((seg, pos), var),
            EqSide::Rhs => self.starts_rhs.insert((seg, pos), var),
        };
        assert!(res.is_none());
    }

    /// Returns the upper bound of the given variable.
    fn get_var_bound(&self, var: &Variable, bounds: &Bounds) -> usize {
        bounds.get_upper_finite(&var).expect("Unbounded variable") as usize
    }

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    fn get_last_var_bound(&self, var: &Variable) -> Option<usize> {
        self.last_var_bounds
            .as_ref()
            .map(|bounds| bounds.get_upper_finite(var).unwrap() as usize)
    }

    /// Encodes the alignment of a segmented pattern with the solution word by matching the respective lengths.
    fn encode_alignment(
        &mut self,
        bounds: &Bounds,
        side: &EqSide,
        dom: &DomainEncoding,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        // Need to clone segments here since we borrow self mutably later to set the start positions
        let segments = self.segments(side).clone();
        let n_seg = segments.length();
        let last_bound = self.last_bound.unwrap_or(0);
        for i in 0..n_seg {
            // Each segment needs to start somewhere
            let mut starts_i = vec![];

            for pos in last_bound..self.bound {
                let svar = pvar();
                self.set_start_position(i, pos, side, svar);
                starts_i.push(svar);
            }

            // The "alignment" constraints ensure that *exactly* one start position is chosen.
            // Thus, the AMO encoding here is not required but redundant.
            // However, we still keep it as it helps the SAT solver.
            // ALO on the other hand seems to slow the solver down, so we omit it
            // TODO: Set flag to enable/disable ALO encoding
            // let amo = self
            //     .segs_starts_amo
            //     .entry((side.clone(), i))
            //     .or_default()
            //     .add(&starts_i);
            // res.extend(amo);
        }

        // Encode start position needs to be 0 for the first segment
        for pos in last_bound..self.bound {
            let var = self.start_position(0, pos, side);
            if pos == 0 {
                // Segment 0 must start at position 0, and at no other position
                res.add_clause(vec![plit(var)]);
            } else {
                res.add_clause(vec![nlit(var)]);
            }
        }

        for (i, s) in segments.iter().enumerate() {
            if i == n_seg - 1 {
                continue;
            }

            // Disable all starts that are too early
            for p in last_bound..segments.prefix_min_len(i, bounds) {
                if p < self.bound {
                    let var = self.start_position(i, p, side);
                    res.add_clause(vec![nlit(var)]);
                }
            }

            match s {
                PatternSegment::Variable(v) => {
                    let start_pos = segments.prefix_min_len(i, bounds);
                    // Incremental either: Length is longer OR start position is later OR Both
                    for pos in start_pos..self.bound {
                        // TODO: Put all "disabled" start-length-pairs is a list and process on next iteration instead of iterating over all pairs and checking the condition
                        let last_vbound = self.get_last_var_bound(v).unwrap_or(0);
                        let vbound = self.get_var_bound(v, bounds);

                        // TODO: Do we really need to iterate over all lengths here or can we just check the last bound?
                        for len in 0..=vbound {
                            // Start position of next segment is i+len
                            let has_length = dom
                                .string()
                                .get_len(v, len)
                                .unwrap_or_else(|| panic!("No length {} for variable {}", len, v));
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            let svar = self.start_position(i, pos, side);

                            // If pos < self.last_bound AND len <= last_vbound, then we already encoded this.
                            // Check if any of the previously invalid position/length pairs became valid
                            // TODO: There must be an easier way to check this
                            if pos < last_bound && len <= last_vbound {
                                if pos + len
                                    >= last_bound.saturating_sub(
                                        segments.suffix_min_len(i, bounds).saturating_sub(1),
                                    )
                                {
                                    if pos + len
                                        < self.bound.saturating_sub(
                                            segments.suffix_min_len(i, bounds).saturating_sub(1),
                                        )
                                    {
                                        // These length/position combinations is now possible

                                        let succ = self.start_position(i + 1, pos + len, side);

                                        res.add_clause(vec![
                                            nlit(svar),
                                            nlit(has_length),
                                            plit(succ),
                                        ]);
                                    } else {
                                        // Still not viable, disable again
                                        let selector = self.bound_selector.unwrap();
                                        res.add_clause(vec![
                                            nlit(selector),
                                            nlit(svar),
                                            nlit(has_length),
                                        ]);
                                    }
                                }
                                continue;
                            }

                            // Encode alignment for new position/length pairs
                            if pos + len
                                < self.bound.saturating_sub(
                                    segments.suffix_min_len(i, bounds).saturating_sub(1),
                                )
                            {
                                let succ = self.start_position(i + 1, pos + len, side);

                                res.add_clause(vec![nlit(svar), nlit(has_length), plit(succ)]);
                            } else {
                                // Cannot start here with length l with current bound
                                let selector = self.bound_selector.unwrap();
                                res.add_clause(vec![nlit(selector), nlit(svar), nlit(has_length)]);
                            }
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    // Only consider the new possible starting positions

                    for pos in segments.prefix_min_len(i, bounds)..self.bound {
                        let len = w.len();
                        let svar = self.start_position(i, pos, side);
                        // Already considered last round
                        if pos < last_bound {
                            // Extends over the last bound, but not over the current bound
                            if pos + len
                                >= last_bound.saturating_sub(segments.suffix_min_len(i, bounds))
                            {
                                // This position was disabled for last bound, but now became viable
                                if pos + len
                                    < self
                                        .bound
                                        .saturating_sub(segments.suffix_min_len(i, bounds))
                                {
                                    let succ = self.start_position(i + 1, pos + len, side);
                                    res.add_clause(vec![nlit(svar), plit(succ)]);
                                } else {
                                    // Still not viable, disable again
                                    res.add_assumption(nlit(svar));
                                }
                            }
                            // Does not extend over the last bound, so we already encoded it and can continue
                            continue;
                        }

                        if pos + len
                            < self
                                .bound
                                .saturating_sub(segments.suffix_min_len(i, bounds))
                        {
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            let succ = self.start_position(i + 1, pos + len, side);

                            res.add_clause(vec![nlit(svar), plit(succ)]);
                        } else {
                            // Cannot start here. Deactivate by means of an assumption, as we might be able to activate it later, when the bound increases

                            res.add_assumption(nlit(svar));
                        }
                    }
                }
            }
        }

        res
    }

    // TODO: use the segments+1 encoding
    fn equal_length(&self, dom: &DomainEncoding, bounds: &Bounds, side: &EqSide) -> EncodingResult {
        let mut clauses = Cnf::new();
        let mut assumptions = indexset! {};
        // Need to clone due to mutable borrow later
        let segments = self.segments(side).clone();

        // Last segment cannot over-extend the bound
        let i = segments.length() - 1;
        let s = segments.get(i);
        let start_pos = segments.prefix_min_len(i, bounds);
        match s {
            PatternSegment::Variable(v) => {
                for pos in 0..self.bound {
                    let vbound = self.get_var_bound(v, bounds);

                    for len in 0..=vbound {
                        let has_len = dom.string().get_len(&v, len).unwrap();

                        if pos + len > self.bound {
                            let svar = self.start_position(i, pos, side);

                            let clause = vec![
                                nlit(self.bound_selector.unwrap()),
                                nlit(svar),
                                nlit(has_len),
                            ];

                            clauses.push(clause);
                        }
                    }
                }
            }
            PatternSegment::Word(w) => {
                for pos in start_pos..self.bound {
                    if pos + w.len() > self.bound {
                        let svar = self.start_position(i, pos, side);
                        assumptions.insert(nlit(svar));
                    }
                }
            }
        }
        EncodingResult::Cnf(clauses, assumptions)
    }

    /// Encodes the matching of each segment of the pattern with the factor of candidate solution word as the respective position.
    fn match_candidate(
        &mut self,
        dom: &DomainEncoding,
        bounds: &Bounds,
        side: &EqSide,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();

        // Need to clone due to mutable borrow later
        let segments = self.segments(side).clone();
        let subs = dom.string();
        let last_bound = self.last_bound.unwrap_or(0);
        let word = self.candidates.encoder_for(side);

        for (i, s) in segments.iter().enumerate() {
            match s {
                PatternSegment::Variable(x) => {
                    for l in 0..=bounds.get_upper_finite(x).unwrap() as usize {
                        let has_len = dom.string().get_len(x, l).unwrap();
                        for p in segments.prefix_min_len(i, bounds)..self.bound {
                            let start_var = self.start_position(i, p, side);
                            if p < last_bound
                                && l < self.get_last_var_bound(x).unwrap_or(0)
                                && l + p
                                    < last_bound.saturating_sub(segments.suffix_min_len(i, bounds))
                            {
                                // Already encoded

                                continue;
                            }

                            if l + p
                                <= self
                                    .bound
                                    .saturating_sub(segments.suffix_min_len(i, bounds))
                            {
                                // If segment starts here, then the next l positions must match substitution of x
                                match l {
                                    1 => {
                                        let m_var: u32 = pvar();
                                        self.var_matches.insert((x.clone(), p, l), m_var);
                                        for c in dom.alphabet().iter() {
                                            let cand_c = word.char_at(p, c);
                                            let sub_c = subs.get_sub(x, 0, c).unwrap();
                                            clauses.push(vec![
                                                nlit(m_var),
                                                nlit(cand_c),
                                                plit(sub_c),
                                            ]);
                                            clauses.push(vec![
                                                nlit(m_var),
                                                plit(cand_c),
                                                nlit(sub_c),
                                            ]);
                                        }
                                        clauses.push(vec![
                                            nlit(start_var),
                                            nlit(has_len),
                                            plit(m_var),
                                        ]);
                                    }
                                    n if n > 1 => {
                                        let m_var = pvar();
                                        let pred_m_var = self.var_matches[&(x.clone(), p, l - 1)];
                                        clauses.push(vec![nlit(m_var), plit(pred_m_var)]);
                                        self.var_matches.insert((x.clone(), p, l), m_var);

                                        // THIS CACHING IS NOT WORKING IF WE HAVE INEQUALITY: The caching assumes we match against the same word, but in case of inequality, we match against two different words, and the cache is invalid.
                                        // Cache this with variable
                                        // I.e., match(x[l-1], cand[p+l-1]) -> EX c. such that they match
                                        // let mv = match self.var_cand_match_cache.get(&(
                                        //     x.clone(),
                                        //     l - 1,
                                        //     p + (l - 1),
                                        // )) {
                                        //     Some(mv) => *mv,
                                        //     None => {
                                        //         let mv = pvar();
                                        //         for c in dom.alphabet().iter() {
                                        //             let cand_c = word.char_at(p + (l - 1), c);
                                        //             let sub_c = subs.get_sub(x, l - 1, c).unwrap();
                                        //             clauses.push(vec![
                                        //                 nlit(mv),
                                        //                 nlit(cand_c),
                                        //                 plit(sub_c),
                                        //             ]);
                                        //             clauses.push(vec![
                                        //                 nlit(mv),
                                        //                 plit(cand_c),
                                        //                 nlit(sub_c),
                                        //             ]);
                                        //         }
                                        //         self.var_cand_match_cache
                                        //             .insert((x.clone(), l - 1, p + (l - 1)), mv);
                                        //         mv
                                        //     }
                                        // };
                                        // clauses.push(vec![nlit(m_var), plit(mv)]);

                                        for c in dom.alphabet().iter() {
                                            let cand_c = word.char_at(p + (l - 1), c);
                                            let sub_c = subs.get_sub(x, l - 1, c).unwrap();
                                            clauses.push(vec![
                                                nlit(m_var),
                                                nlit(cand_c),
                                                plit(sub_c),
                                            ]);
                                            clauses.push(vec![
                                                nlit(m_var),
                                                plit(cand_c),
                                                nlit(sub_c),
                                            ]);
                                        }

                                        clauses.push(vec![
                                            nlit(start_var),
                                            nlit(has_len),
                                            plit(m_var),
                                        ]);
                                    }
                                    _ => {}
                                }
                            }
                        }
                        // Next position in variable, if exists, is lambda
                        if self.get_last_var_bound(x).unwrap_or(0) <= l
                            && l < bounds.get_upper_finite(x).unwrap() as usize
                        {
                            // If variable is assigned length l, then the position x[l] (and implicitly all following) must be lambda
                            let sub_lambda = subs.get_sub(x, l, LAMBDA).unwrap();

                            clauses.push(vec![nlit(has_len), plit(sub_lambda)]);
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    for p in segments.prefix_min_len(i, bounds)
                        ..self
                            .bound
                            .saturating_sub(w.len().saturating_sub(1))
                            .saturating_sub(segments.suffix_min_len(i, bounds))
                    {
                        if p < last_bound
                            && p < last_bound
                                .saturating_sub(w.len().saturating_sub(1))
                                .saturating_sub(segments.suffix_min_len(i, bounds))
                        {
                            // Already encoded
                            continue;
                        }

                        let start_var = self.start_position(i, p, side);
                        // If segment starts here, then the next |w| positions must match w
                        // S_i^p  -> /\{k=0...|w|} c_{p+j} = w[k]

                        for (k, c) in w.iter().enumerate() {
                            let cand_var = word.char_at(p + k, *c);
                            clauses.push(vec![nlit(start_var), plit(cand_var)]);
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    /// Encodes that after the last segment, the solution word must be lambda.
    fn lambda_suffix(
        &self,
        bounds: &Bounds,
        side: &EqSide,
        dom: &DomainEncoding,
    ) -> EncodingResult {
        let word = self.candidates.encoder_for(side);
        let segments = self.segments(side);
        if segments.length() == 0 {
            return EncodingResult::Trivial(true);
        }
        let last_bound = self.last_bound.unwrap_or(0);
        let mut clauses = Cnf::new();
        let last = segments.length() - 1;

        match &segments.segments[last] {
            PatternSegment::Variable(x) => {
                for p in 0..self.bound {
                    for l in 0..=bounds.get_upper_finite(x).unwrap() as usize {
                        // Filter out l,p pairs that have been encoded already, i.e. p+l < last_bound
                        if p < last_bound
                            && l < self.get_last_var_bound(x).unwrap_or(0)
                            && p + l < last_bound
                        {
                            continue;
                        }
                        if p + l < self.bound {
                            let start_var = self.start_position(last, p, side);
                            let has_len = dom.string().get_len(x, l).unwrap();
                            let cand_var = word.char_at(p + l, LAMBDA);

                            clauses.push(vec![nlit(start_var), nlit(has_len), plit(cand_var)]);
                        }
                    }
                }
            }
            PatternSegment::Word(w) => {
                for p in 0..self.bound {
                    // 🔧 Skip p which are already encoded, i.e., skip p with p+w.len() < last_bound

                    if p + w.len() >= last_bound && p + w.len() < self.bound {
                        let start_var = self.start_position(last, p, side);
                        let cand_var = word.char_at(p + w.len(), LAMBDA);
                        clauses.push(vec![nlit(start_var), plit(cand_var)]);
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn encode_mismatch(&mut self, dom: &DomainEncoding) -> EncodingResult {
        let mut result = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(0);
        let lhs = self.candidates.lhs_encoder();
        let rhs = self.candidates.rhs_encoder();
        let mut new_mismatch_selectors = vec![];
        for b in last_bound.saturating_sub(1)..self.bound {
            let v = pvar();
            new_mismatch_selectors.push(v);
            // If v is true, then there is a mismatch at position b
            for c in dom.alphabet().iter() {
                let lhs_c = lhs.char_at(b, c);
                let rhs_c = rhs.char_at(b, c);
                result.add_clause(vec![nlit(v), nlit(lhs_c), nlit(rhs_c)]);
            }
            let lhs_lambda = lhs.char_at(b, LAMBDA);
            let rhs_lambda = rhs.char_at(b, LAMBDA);

            result.add_clause(vec![nlit(v), nlit(lhs_lambda), nlit(rhs_lambda)]);
        }

        result.extend(self.mismatch_alo.add(&new_mismatch_selectors));

        result
    }
}

impl LiteralEncoder for WordEquationEncoder {
    fn encode(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        self.round += 1;

        let mut res = EncodingResult::empty();

        let bound = if self.pol {
            min(
                FilledPattern::fill(&self.equation.lhs(), bounds).length(),
                FilledPattern::fill(&self.equation.rhs(), bounds).length(),
            )
        } else {
            max(
                FilledPattern::fill(&self.equation.lhs(), bounds).length(),
                FilledPattern::fill(&self.equation.rhs(), bounds).length(),
            )
        } + 1;
        // we need to add 1 to the bound to allow empty variables to start somewhere
        // For example in aX = a, if we set the bound to 1, then variable X cannot start at position 2 (even if empty).

        assert!(bound >= self.bound, "Bound cannot shrink");
        assert!(bound > 0);

        // If the bound stays the same, the previous rounds' encoding is still correct.
        // In this case, we need to return the same set of assumptions.
        if bound == self.bound {
            let mut same_bounds = true;

            if let Some(last_bounds) = self.last_var_bounds.as_ref() {
                for v in self.equation.variables() {
                    if last_bounds.get_upper_finite(&v) != bounds.get_upper_finite(&v) {
                        same_bounds = false;
                        break;
                    }
                }
            }
            if same_bounds {
                if let Some(v) = self.bound_selector {
                    res.add_assumption(plit(v));
                }
                log::trace!("Bound did not change, returning assumption from previous round",);
                return Ok(res);
            }
        }

        if let Some(v) = self.bound_selector {
            // Deactivate all clauses that were only valid for the previous bound
            res.extend(EncodingResult::cnf(vec![vec![nlit(v)]]));
        }
        self.bound = bound;

        // New selector for this round
        let selector = pvar();
        self.bound_selector = Some(selector);
        res.add_assumption(plit(selector));

        // Encode the candidates
        let cand_enc = self.candidates.encode(bound, dom);
        log::trace!("Clauses for candidates: {}", cand_enc.clauses());
        res.extend(cand_enc);

        // Encode alignment of segments with candidates LHS
        let ts = Instant::now();
        let align_enc = self.encode_alignment(bounds, &EqSide::Lhs, dom);
        log::trace!(
            "Clauses for alignments LHS: {} ({} ms)",
            align_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.extend(align_enc);

        // Encode alignment of segments with candidates RHS
        let ts = Instant::now();
        let align_enc = self.encode_alignment(bounds, &EqSide::Rhs, dom);
        log::trace!(
            "Clauses for alignments RHS: {} ({} ms)",
            align_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.extend(align_enc);

        let suffix_enc_lhs = self.lambda_suffix(bounds, &EqSide::Lhs, dom);
        log::trace!(
            "Clauses for lambda suffix lhs: {}",
            suffix_enc_lhs.clauses()
        );
        res.extend(suffix_enc_lhs);

        let suffix_enc_rhs = self.lambda_suffix(bounds, &EqSide::Rhs, dom);
        log::trace!(
            "Clauses for lambda suffix rhs: {}",
            suffix_enc_rhs.clauses()
        );
        res.extend(suffix_enc_rhs);

        let ts = Instant::now();
        let vars_match_lhs_enc = self.match_candidate(dom, bounds, &EqSide::Lhs);

        log::trace!(
            "Clauses for variable matching LHS: {} ({} ms)",
            vars_match_lhs_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.extend(vars_match_lhs_enc);

        let ts = Instant::now();
        let vars_match_rhs_enc = self.match_candidate(dom, bounds, &EqSide::Rhs);
        log::trace!(
            "Clauses for variable matching RHS: {} ({} ms)",
            vars_match_rhs_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.extend(vars_match_rhs_enc);

        if !self.candidates.is_equality() {
            let mismatch_enc = self.encode_mismatch(dom);
            log::trace!("Clauses for mismatch: {}", mismatch_enc.clauses());
            res.extend(mismatch_enc);
        } else {
            // On the equality case, both sides must be of length bound
            // If one filled patter is longer than the other, then the bound must be limited to the shorter one
            res.extend(self.equal_length(dom, bounds, &EqSide::Lhs));
            res.extend(self.equal_length(dom, bounds, &EqSide::Rhs));
        }

        // Store variable bounds for next round
        self.last_var_bounds = Some(bounds.clone());
        self.last_bound = Some(self.bound);
        Ok(res)
    }

    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn print_debug(&self, solver: &cadical::Solver, dom: &DomainEncoding) {
        let lhs = self.candidates.lhs_encoder();
        let rhs = self.candidates.rhs_encoder();
        let mut lhs_sol = String::new();
        let mut rhs_sol = String::new();
        for pos in 0..self.bound {
            for c in dom.alphabet().iter() {
                if let Some(true) = solver.value(plit(lhs.char_at(pos, c))) {
                    lhs_sol.push_str(c.escape_default().to_string().as_str());
                }
                if let Some(true) = solver.value(plit(rhs.char_at(pos, c))) {
                    rhs_sol.push_str(c.escape_default().to_string().as_str());
                }
            }
            if let Some(true) = solver.value(plit(lhs.char_at(pos, LAMBDA))) {
                lhs_sol.push_str("λ");
            }
            if let Some(true) = solver.value(plit(rhs.char_at(pos, LAMBDA))) {
                rhs_sol.push_str("λ");
            }
        }
        println!("SOLUTION FOR {} (BOUND: {})", self.equation, self.bound);
        println!("\tLHS: {}", lhs_sol);
        println!("\tRHS: {}", rhs_sol);
        println!(
            "\t Bound selector {} is {}",
            self.bound_selector.unwrap(),
            solver.value(plit(self.bound_selector.unwrap())).unwrap()
        );
        println!("\tLHS POSITIONS:");
        for i in 0..self.segments(&EqSide::Lhs).length() {
            for p in 0..self.bound {
                let v = self.start_position(i, p, &EqSide::Lhs);

                if let Some(true) = solver.value(plit(v)) {
                    println!(
                        "\t\t- {} starts at {} ({})",
                        self.segments(&EqSide::Lhs).segments[i],
                        p,
                        v
                    );
                }
            }
        }
        println!("\tRHS POSITIONS:");
        for i in 0..self.segments(&EqSide::Rhs).length() {
            for p in 0..self.bound {
                let v = self.start_position(i, p, &EqSide::Rhs);
                if let Some(true) = solver.value(plit(v)) {
                    println!(
                        "\t\t- {} starts at {} ({})",
                        self.segments(&EqSide::Rhs).segments[i],
                        p,
                        v
                    );
                }
            }
        }
        println!("\tASSIGNED LENGTHS");
        for v in &self.equation.variables() {
            for l in 0..=self
                .last_var_bounds
                .as_ref()
                .unwrap()
                .get_upper_finite(v)
                .unwrap() as usize
            {
                let lvar = dom.string().get_len(v, l).unwrap();

                if let Some(true) = solver.value(plit(lvar)) {
                    println!("\t\t- |{}| = {} ({})", v, l, lvar);
                }
            }
        }
    }
}

/* Pretty Printing */

impl Display for PatternSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternSegment::Variable(v) => write!(f, "{}", v),
            PatternSegment::Word(w) => write!(f, "\"{}\"", w.iter().collect::<String>()),
        }
    }
}

impl Display for EqSide {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EqSide::Lhs => write!(f, "LHS"),
            EqSide::Rhs => write!(f, "RHS"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alphabet::Alphabet,
        bounds::{
            step::{update_bounds, BoundStep},
            Interval,
        },
        context::{Context, Sort},
        ir::{parse_simple_equation, Substitutable, TrivialReducible},
    };
    use std::collections::HashSet;

    use super::*;
    use cadical::Solver;

    use crate::encode::domain::DomainEncoder;

    #[test]
    fn segment_single_var() {
        let mut ctx = Context::default();
        let var = ctx.new_temp_var(Sort::String);
        let p = Pattern::variable(&var);
        let segs = SegmentedPattern::new(&p);
        assert_eq!(segs.length(), 1);
        assert_eq!(
            segs.segments[0],
            PatternSegment::Variable(var.as_ref().clone())
        );
    }

    #[test]
    fn segment_single_const() {
        let constant = "foo";
        let p = Pattern::constant(constant);
        let segs = SegmentedPattern::new(&p);
        assert_eq!(segs.length(), 1);
        assert_eq!(
            segs.segments[0],
            PatternSegment::Word(constant.chars().collect())
        );
    }

    #[test]
    fn segment_empty() {
        // The empty pattern must be encoded as a single segment with the empty word
        let p = Pattern::empty();
        let segs = SegmentedPattern::new(&p);
        assert_eq!(segs.length(), 1);
    }

    #[test]
    fn segment_vars_consts() {
        let mut ctx = Context::default();
        let var1 = ctx.new_temp_var(Sort::String).as_ref().clone();
        let var2 = ctx.new_temp_var(Sort::String).as_ref().clone();

        let mut p = Pattern::empty();
        p.push_var(var1.clone())
            .push_word("foo")
            .push_var(var1.clone())
            .push_var(var2.clone())
            .push_word("foo")
            .push_word("bar");
        let segs = SegmentedPattern::new(&p);
        assert_eq!(segs.length(), 5);
        assert_eq!(segs.segments[0], PatternSegment::Variable(var1.clone()));
        assert_eq!(
            segs.segments[1],
            PatternSegment::Word("foo".chars().collect())
        );
        assert_eq!(segs.segments[2], PatternSegment::Variable(var1.clone()));
        assert_eq!(segs.segments[3], PatternSegment::Variable(var2));
        assert_eq!(
            segs.segments[4],
            PatternSegment::Word("foobar".chars().collect())
        );
    }

    fn solve_align(
        eq: &WordEquation,
        bounds: Bounds,
        alphabet: &Alphabet,
        ctx: &mut Context,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();

        let mut dom_encoder = DomainEncoder::new(alphabet.clone());
        let dom_cnf = dom_encoder.encode(&bounds, ctx);
        encoding.extend(dom_cnf);

        let mut encoder = WordEquationEncoder::new(eq.clone(), true);
        encoding.extend(encoder.encode(&bounds, dom_encoder.encoding()).unwrap());

        let mut solver: Solver = Solver::default();
        let mut assumptions = HashSet::new();
        match encoding {
            EncodingResult::Cnf(cnf, assms) => {
                for clause in cnf {
                    solver.add_clause(clause);
                }
                assumptions.extend(assms);
            }
            EncodingResult::Trivial(false) => return Some(false),
            EncodingResult::Trivial(true) => return Some(true),
        }
        let res = solver.solve_with(assumptions.into_iter());
        if let Some(true) = res {
            let model = dom_encoder.encoding().get_model(&solver);

            println!("\n========================\n");
            for i in 0..encoder.segments(&EqSide::Rhs).length() {
                for p in 0..encoder.bound {
                    let v = encoder.start_position(i, p, &EqSide::Rhs);
                    if let Some(true) = solver.value(plit(v)) {
                        println!(
                            "{} starts at {}",
                            encoder.segments(&EqSide::Rhs).segments[i],
                            p
                        );
                    }
                }
            }
            for v in &eq.variables() {
                for l in 0..=bounds.get_upper_finite(v).unwrap() as usize {
                    let lvar = dom_encoder.encoding().string().get_len(v, l).unwrap();

                    if let Some(true) = solver.value(plit(lvar)) {
                        println!("|{}| = {}", v, bounds.get_upper_finite(v).unwrap());
                    }
                }
            }

            let substituted = eq.apply_substitution(&model).is_trivial();
            assert_eq!(
                substituted,
                Some(true),
                "{} is not a solution for {}: {:?} != {:?}",
                model,
                eq,
                eq.lhs().apply_substitution(&model),
                eq.rhs().apply_substitution(&model)
            );
        }
        res
    }

    fn solve_align_incremental(
        eq: &WordEquation,
        limit: usize,
        alphabet: &Alphabet,
        ctx: &mut Context,
    ) -> Option<bool> {
        let mut encoder = WordEquationEncoder::new(eq.clone(), true);

        let mut dom_encoder = DomainEncoder::new(alphabet.clone());

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 1));
        }

        let mut result = None;

        let mut solver: Solver = Solver::new();

        fn clamp_uppers(bounds: Bounds, limit: usize) -> Bounds {
            let mut clamped = Bounds::default();
            for (v, i) in bounds.iter() {
                let new_upper = i.upper().min(limit.into());
                clamped.set(v.clone(), Interval::new(i.lower(), new_upper));
            }
            clamped
        }

        let mut last_round = false;
        while !last_round {
            last_round |= bounds.iter().all(|(_, i)| i.upper() >= limit.into());
            let mut encoding = EncodingResult::empty();

            encoding.extend(dom_encoder.encode(&bounds, &ctx));
            encoding.extend(encoder.encode(&bounds, dom_encoder.encoding()).unwrap());
            result = match encoding {
                EncodingResult::Cnf(cnf, assm) => {
                    for clause in cnf {
                        solver.add_clause(clause);
                    }
                    solver.solve_with(assm.into_iter())
                }
                EncodingResult::Trivial(f) => Some(f),
            };

            bounds = update_bounds(&bounds, BoundStep::NextSquare);
            bounds = clamp_uppers(bounds, limit);
        }
        if let Some(true) = result {
            let model = dom_encoder.encoding().get_model(&solver);

            for i in 0..encoder.segments(&EqSide::Rhs).length() {
                for p in 0..encoder.bound {
                    let v = encoder.start_position(i, p, &EqSide::Rhs);
                    if let Some(true) = solver.value(plit(v)) {
                        println!(
                            "{} starts at {}",
                            encoder.segments(&EqSide::Rhs).segments[i],
                            p
                        );
                    }
                }
            }
            for i in 0..encoder.segments(&EqSide::Lhs).length() {
                for p in 0..encoder.bound {
                    let v = encoder.start_position(i, p, &EqSide::Lhs);
                    if let Some(true) = solver.value(plit(v)) {
                        println!(
                            "{} starts at {}",
                            encoder.segments(&EqSide::Lhs).segments[i],
                            p
                        );
                    }
                }
            }
            println!("Bounds: {:?}", bounds);
            println!("{:?}", dom_encoder.encoding().string());
            for v in &eq.variables() {
                for l in 0..=bounds.get_upper_finite(v).unwrap() as usize {
                    let lvar = dom_encoder
                        .encoding()
                        .string()
                        .get_len(v, l)
                        .expect(format!("no length {}:{}", v, l).as_str());

                    if let Some(true) = solver.value(plit(lvar)) {
                        println!("|{}| = {}", v, bounds.get_upper_finite(v).unwrap());
                    }
                }
            }

            let substituted = eq.apply_substitution(&model).is_trivial();
            assert_eq!(
                substituted,
                Some(true),
                "{} is not a solution for {}: {:?} != {:?}",
                model,
                eq,
                eq.lhs().apply_substitution(&model),
                eq.rhs().apply_substitution(&model)
            );
        }
        result
    }

    #[test]
    fn align_incremental_sat() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "abc", &mut ctx);

        let res = solve_align_incremental(&eq, 5, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_empty_eq() {
        let mut ctx = Context::default();
        let eq = WordEquation::new(Pattern::from(vec![]), Pattern::from(vec![]));
        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_trivial_sat_consts() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("bar", "bar", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_trivial_unsat_consts() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("bar", "barr", &mut ctx);
        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn align_trivial_unsat_consts_2() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("bar", "foo", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn align_trivial_sat_const_var() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "abc", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 5));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_trivial_sat_var_eq_same_var() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("A", "A", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_trivial_sat_var_eq_other_var() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("A", "B", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_sat_commute() {
        // AB = BA
        let mut ctx = Context::default();

        let eq = parse_simple_equation("AB", "BA", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 10));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_sat_pattern_const() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("aXc", "abc", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 1));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_sat_two_patterns_unsat() {
        let mut ctx = Context::default();

        let eq = parse_simple_equation("aXb", "YXc", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 2));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn align_sat_two_patterns_sat() {
        let mut ctx = Context::default();

        let eq = parse_simple_equation("aXb", "YbX", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 2));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_trivial_unsat_const_var_too_small() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("X", "foo", &mut ctx);

        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var.clone(), Interval::new(0, 1));
        }

        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn align_sat_t1i74() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation(
            "A",
            "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd",
            &mut ctx,
        );
        let mut bounds = Bounds::default();
        for var in eq.variables() {
            bounds.set(var, Interval::new(0, 50));
        }
        let res = solve_align(&eq, bounds, &eq.constants().into_iter().collect(), &mut ctx);

        assert!(matches!(res, Some(true)));
    }
    #[test]
    fn align_sat_t1i74_incremental() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation(
            "A",
            "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd",
            &mut ctx,
        );
        let res = solve_align_incremental(&eq, 50, &eq.constants().into_iter().collect(), &mut ctx);

        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_sat_t1i1() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation(
            "cfcbbAadeeaecAgebegeecafegebdbagddaadbddcaeeebfabfefabfacdgAgaabg",
            "AfcbbAaIegeeAaD",
            &mut ctx,
        );

        let res = solve_align_incremental(&eq, 50, &eq.constants().into_iter().collect(), &mut ctx);

        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn align_sat_t1i97() {
        let mut ctx = Context::default();
        let eq = parse_simple_equation("AccAbccB", "CccAbDbcCcA", &mut ctx);
        let res = solve_align_incremental(&eq, 50, &eq.constants().into_iter().collect(), &mut ctx);

        assert!(matches!(res, Some(true)));
    }
}
