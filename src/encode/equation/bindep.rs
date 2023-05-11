use std::cmp::max;
use std::collections::HashMap;
use std::fmt::Display;

use crate::encode::card::{amo, exactly_one};
use crate::encode::substitution::SubstitutionEncoding;
use crate::encode::{EncodingResult, FilledPattern, PredicateEncoder, VariableBounds, LAMBDA};
use crate::model::words::{Pattern, Symbol, WordEquation};
use crate::model::Variable;
use crate::sat::{as_lit, neg, pvar, Cnf, PVar};
use indexmap::{IndexMap, IndexSet};

use super::WordEquationEncoder;

#[derive(Clone, Debug, PartialEq, Eq)]
enum PatternSegment {
    /// A string variable
    Variable(Variable),
    /// A string constant
    Word(Vec<char>),
}

impl Display for PatternSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternSegment::Variable(v) => write!(f, "{}", v),
            PatternSegment::Word(w) => write!(f, "\"{}\"", w.iter().collect::<String>()),
        }
    }
}

#[derive(Clone, Debug)]
struct SegmentedPattern {
    segments: Vec<PatternSegment>,
}

impl SegmentedPattern {
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

    /// Counts the number of constants in the pattern
    fn consts(&self) -> usize {
        self.segments
            .iter()
            .filter_map(|s| match s {
                PatternSegment::Variable(_) => None,
                PatternSegment::Word(w) => Some(w),
            })
            .map(|w| w.len())
            .sum()
    }

    /// Returns true if the segment at position i is a variable, panics if i is out of bounds.
    fn is_var(&self, i: usize) -> bool {
        match self.get(i) {
            PatternSegment::Variable(_) => true,
            PatternSegment::Word(_) => false,
        }
    }

    /// Returns true if the segment at position i is a constant, panics if i is out of bounds.
    fn is_word(&self, i: usize) -> bool {
        !self.is_var(i)
    }

    /// Returns the earliest position at which the segment at position i can start.
    fn earliest_start(&self, i: usize) -> usize {
        let mut pos = 0;
        for j in 0..i {
            if let PatternSegment::Word(w) = self.get(j) {
                pos += w.len();
            }
        }
        pos
    }

    fn followers(&self, i: usize) -> usize {
        let mut f = 0;
        for j in i + 1..self.length() {
            if let PatternSegment::Word(w) = self.get(j) {
                f += w.len();
            }
        }
        f
    }
}

pub struct BindepEncoder {
    /// The original word equation
    equation: WordEquation,

    /// Upper bound for the solution word, is 0 prior to first round.
    bound: usize,

    /// Upper bound used in previous round, is None prior to first round.
    last_bound: Option<usize>,

    /// The substitution encoding of the left-hand side. Maps a positions and a character to a variable that is true if the character is at the position.
    subs_lhs: HashMap<(usize, char), PVar>,
    /// The substitution encoding of the right-hand side. Maps a positions and a character to a variable that is true if the character is at the position.
    subs_rhs: HashMap<(usize, char), PVar>,

    /// Counts the rounds, is 0 prior to the first round and is incremented each call to `encode`.
    round: usize,

    starts_lhs: IndexMap<(usize, usize), PVar>,
    starts_rhs: IndexMap<(usize, usize), PVar>,
    segments_lsh: Option<SegmentedPattern>,
    segments_rhs: Option<SegmentedPattern>,
    cand_positions: IndexMap<(usize, char), PVar>,
    var_lens: IndexMap<(Variable, usize), PVar>,
}

impl BindepEncoder {
    /// Returns a map that maps pairs of positions and characters to a propositional variable that is true if the character is at the position.
    fn encode_candiates(
        &self,
        bound: usize,
        alphabet: &IndexSet<char>,
    ) -> (EncodingResult, IndexMap<(usize, char), PVar>) {
        let mut res = EncodingResult::empty();
        let mut cand_positions = IndexMap::new();

        for pos in 0..bound {
            let mut p_choices = vec![];
            for c in alphabet {
                let v = pvar();
                p_choices.push(v);
                cand_positions.insert((pos, *c), v);
            }
            let v_lambda = pvar();
            p_choices.push(v_lambda);
            cand_positions.insert((pos, LAMBDA), v_lambda);
            let cnf = exactly_one(&p_choices);

            // If a position is lambda, then only lambda may follow
            if pos > 0 {
                let last_lambda = cand_positions[&(pos - 1, LAMBDA)];
                res.join(EncodingResult::cnf(vec![vec![
                    neg(last_lambda),
                    as_lit(v_lambda),
                ]]));
            }

            res.join(EncodingResult::cnf(cnf));
        }
        (res, cand_positions)
    }

    /// Returns map that maps pairs of positions within a candidate solution word to a propositional variable that is true if the positions are equal.
    fn encode_match_vars(
        &self,
        candidate: &IndexMap<(usize, char), PVar>,
        alphabet: &IndexSet<char>,
        bound: usize,
    ) -> (EncodingResult, IndexMap<(usize, usize), PVar>) {
        let mut clauses = Cnf::new();
        let mut matches = IndexMap::new();
        for i in 0..bound {
            for j in i..bound {
                let m_ij = pvar();
                // m_ij -> (c_i=c -> c_j=c)
                for c in alphabet {
                    let cand_i_c = as_lit(candidate[&(i, *c)]);
                    let cand_j_c = as_lit(candidate[&(j, *c)]);

                    clauses.push(vec![neg(m_ij), -cand_i_c, cand_j_c]);
                    // (c_i=c -> c_j=c) -> m_ij
                    // <=> -(c_i=c -> c_j=c) \/ m_ij
                    // <=> -(-c_i=c \/ c_j=c) \/ m_ij
                    // <=> (c_i=c /\ -c_j=c) \/ m_ij <=> (c_i = c \/ m_ij) /\ (-c_j=c \/ m_ij)
                    //clauses.push(vec![cand_i_c, as_lit(m_ij)]);
                    //clauses.push(vec![-cand_j_c, as_lit(m_ij)]);
                }
                matches.insert((i, j), m_ij);
            }
        }
        (EncodingResult::cnf(clauses), matches)
    }

    /// Returns a map that maps pairs of variables and lengths to a propositional variable that is true if the variable has the given length.
    fn encode_var_lenghts(
        &self,
        vars: &IndexSet<Variable>,
        bounds: &VariableBounds,
    ) -> (EncodingResult, IndexMap<(Variable, usize), PVar>) {
        let mut cnf = Cnf::new();
        let mut len_cands = IndexMap::new();
        for v in vars {
            let mut len_choices = vec![];
            for len in 0..=bounds.get(v) {
                let choice = pvar();
                len_choices.push(choice);
                len_cands.insert((v.clone(), len), choice);
            }
            let eo = exactly_one(&len_choices);
            cnf.extend(eo);
        }

        (EncodingResult::cnf(cnf), len_cands)
    }

    /// Returns map that maps pairs of segment indices and start positions to a propositional variable that is true if the segment starts at the position.
    fn encode_alignment(
        &self,
        segments: &SegmentedPattern,
        lens: &IndexMap<(Variable, usize), PVar>,
        bounds: &VariableBounds,
        bound: usize,
    ) -> (EncodingResult, IndexMap<(usize, usize), PVar>) {
        let mut clauses = Cnf::new();
        let mut starts = IndexMap::new();
        let n_seg = segments.length();

        for i in 0..n_seg {
            // Each segment needs to start somewhere
            let mut starts_i = vec![];
            for pos in 0..bound {
                let svar = pvar();
                starts.insert((i, pos), svar);
                starts_i.push(svar);
            }
            //clauses.push(starts_i.iter().map(|v| as_lit(*v)).collect_vec()); // Not required and slows down the solver
            clauses.extend(amo(&starts_i)); // No required but seems to help the SAT solver
        }

        for pos in 0..bound {
            if pos == 0 {
                // Segment 0 must start at position 0, and at no other position
                clauses.push(vec![as_lit(starts[&(0, pos)])]);
            } else {
                clauses.push(vec![neg(starts[&(0, pos)])]);
            }
        }

        for (i, s) in segments.segments.iter().enumerate() {
            if i == n_seg - 1 {
                continue;
            }
            // Disable all starts that are too early
            for p in 0..segments.earliest_start(i) {
                clauses.push(vec![neg(starts[&(i, p)])]);
            }
            match s {
                PatternSegment::Variable(v) => {
                    for pos in segments.earliest_start(i)..bound {
                        let vbound = bounds.get(v);
                        for len in 0..=vbound {
                            // Start position of next segment is i+len
                            let len_var = lens[&(v.clone(), len)];
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            let svar = starts[&(i, pos)];
                            if pos + len < bound - (segments.followers(i).saturating_sub(1)) {
                                clauses.push(vec![
                                    neg(svar),
                                    neg(len_var),
                                    as_lit(starts[&(i + 1, pos + len)]),
                                ]);
                            } else {
                                // Cannot start here with length l (ASSUME!)
                                clauses.push(vec![neg(svar), neg(len_var)]);
                            }
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    for pos in segments.earliest_start(i)..bound {
                        let len = w.len();
                        let svar = starts[&(i, pos)];
                        if pos + len < bound - segments.followers(i) {
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            clauses.push(vec![neg(svar), as_lit(starts[&(i + 1, pos + len)])]);
                        } else {
                            // Cannot start here (ASSUME!)
                            clauses.push(vec![neg(svar)]);
                        }
                    }
                }
            }
        }

        (EncodingResult::cnf(clauses), starts)
    }

    fn match_constants_candidate(
        &self,
        segments: &SegmentedPattern,
        starts: &IndexMap<(usize, usize), PVar>,
        candidate: &IndexMap<(usize, char), PVar>,
        bound: usize,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        for (i, s) in segments.segments.iter().enumerate() {
            match s {
                PatternSegment::Variable(_) => {}
                PatternSegment::Word(w) => {
                    for p in
                        segments.earliest_start(i)..bound - (w.len() - 1) - segments.followers(i)
                    {
                        let start_var = starts[&(i, p)];
                        // If segment starts here, then the next |w| positions must match w
                        // S_i^p  -> /\{k=0...|w|} c_{p+j} = w[k]

                        for (k, c) in w.iter().enumerate() {
                            let cand_var = candidate[&(p + k, *c)];
                            clauses.push(vec![neg(start_var), as_lit(cand_var)]);
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn match_var_candidate(
        &self,
        segments: &SegmentedPattern,
        starts: &IndexMap<(usize, usize), PVar>,
        candidate: &IndexMap<(usize, char), PVar>,
        lens: &IndexMap<(Variable, usize), PVar>,
        subs: &SubstitutionEncoding,
        bounds: &VariableBounds,
        bound: usize,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        for (i, s) in segments.segments.iter().enumerate() {
            match s {
                PatternSegment::Variable(x) => {
                    for l in 0..=bounds.get(x) {
                        let len_var = lens[&(x.clone(), l)];
                        for p in segments.earliest_start(i)..bound {
                            let start_var = starts[&(i, p)];

                            if l + p <= bound - segments.followers(i) {
                                // If segment starts here, then the next |w| positions must match substitution of x
                                for k in 0..l {
                                    for c in subs.alphabet() {
                                        let cand_c = candidate[&(p + k, *c)];
                                        let sub_c = subs.get(x, k, *c).unwrap();
                                        clauses.push(vec![
                                            neg(start_var),
                                            neg(len_var),
                                            neg(cand_c),
                                            as_lit(sub_c),
                                        ]);
                                        clauses.push(vec![
                                            neg(start_var),
                                            neg(len_var),
                                            as_lit(cand_c),
                                            neg(sub_c),
                                        ]);
                                    }
                                }
                            }
                        }
                        // Next position in variable, if exists, is lambda
                        if l < bounds.get(x) {
                            let sub_lambda = subs.get(x, l, LAMBDA).unwrap();
                            clauses.push(vec![neg(len_var), as_lit(sub_lambda)]);
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    for p in
                        segments.earliest_start(i)..bound - (w.len() - 1) - segments.followers(i)
                    {
                        let start_var = starts[&(i, p)];
                        // If segment starts here, then the next |w| positions must match w
                        // S_i^p  -> /\{k=0...|w|} c_{p+j} = w[k]

                        for (k, c) in w.iter().enumerate() {
                            let cand_var = candidate[&(p + k, *c)];
                            clauses.push(vec![neg(start_var), as_lit(cand_var)]);
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn match_vars_inner(
        &self,
        segments: &SegmentedPattern,
        starts: &IndexMap<(usize, usize), PVar>,
        lens: &IndexMap<(Variable, usize), PVar>,
        matches: &IndexMap<(usize, usize), PVar>,
        bounds: &VariableBounds,
        bound: usize,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        for (i, s) in segments.segments.iter().enumerate() {
            for (j, ss) in segments.segments.iter().enumerate().skip(i + 1) {
                if let (PatternSegment::Variable(x), PatternSegment::Variable(y)) = (s, ss) {
                    if x == y {
                        // Same variable occurs at different positions, encode matching
                        for posx in 0..bound {
                            for posy in posx..bound {
                                let vbound = bounds.get(x);
                                for len in 0..std::cmp::min(vbound, bound - posy) {
                                    let var_len = lens[&(x.clone(), len)]; // Equivalent to len for y, as x= y
                                    let startx = starts[&(i, posx)];
                                    let starty = starts[&(j, posy)];
                                    for k in 0..len {
                                        let match_var = matches[&(posx + k, posy + k)];
                                        clauses.push(vec![
                                            neg(startx),
                                            neg(starty),
                                            neg(var_len),
                                            as_lit(match_var),
                                        ]);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn match_vars_outer(
        &self,
        segments_a: &SegmentedPattern,
        segments_b: &SegmentedPattern,
        starts_a: &IndexMap<(usize, usize), PVar>,
        starts_b: &IndexMap<(usize, usize), PVar>,
        lens: &IndexMap<(Variable, usize), PVar>,
        matches: &IndexMap<(usize, usize), PVar>,
        bounds: &VariableBounds,
        bound: usize,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        for (i, s) in segments_a.segments.iter().enumerate() {
            for (j, ss) in segments_b.segments.iter().enumerate() {
                // .skip(i) {
                if let (PatternSegment::Variable(x), PatternSegment::Variable(y)) = (s, ss) {
                    if x == y {
                        // Same variable occurs at different positions, encode matching
                        for posx in 0..bound {
                            for posy in posx..bound {
                                let vbound = bounds.get(x);
                                for len in
                                    0..std::cmp::min(vbound, bound - std::cmp::max(posx, posy))
                                {
                                    let var_len = lens[&(x.clone(), len)]; // Equivalent to len for y, as x= y
                                    let startx = starts_a[&(i, posx)];
                                    let starty = starts_b[&(j, posy)];
                                    for k in 0..len {
                                        let match_var = matches[&(posx + k, posy + k)];
                                        clauses.push(vec![
                                            neg(startx),
                                            neg(starty),
                                            neg(var_len),
                                            as_lit(match_var),
                                        ]);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn lambda_suffix(
        &self,
        segments: &SegmentedPattern,
        starts: &IndexMap<(usize, usize), PVar>,
        lens: &IndexMap<(Variable, usize), PVar>,
        candidate: &IndexMap<(usize, char), PVar>,
        bounds: &VariableBounds,
        bound: usize,
    ) -> EncodingResult {
        if segments.length() == 0 {
            return EncodingResult::Trivial(true);
        }
        let mut clauses = Cnf::new();
        let last = segments.length() - 1;
        match &segments.segments[last] {
            PatternSegment::Variable(x) => {
                for p in 0..bound {
                    for l in 0..=bounds.get(x) {
                        if p + l < bound {
                            let start_var = starts[&(last, p)];
                            let len_var = lens[&(x.clone(), l)];
                            let cand_var = candidate[&(p + l, LAMBDA)];
                            clauses.push(vec![neg(start_var), neg(len_var), as_lit(cand_var)]);
                        }
                    }
                }
            }
            PatternSegment::Word(w) => {
                for p in 0..bound {
                    if p + w.len() < bound {
                        let start_var = starts[&(last, p)];
                        let cand_var = candidate[&(p + w.len(), LAMBDA)];
                        clauses.push(vec![neg(start_var), as_lit(cand_var)]);
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn bridge_substitutions(
        &self,
        segments_a: &SegmentedPattern,
        segments_b: &SegmentedPattern,
        starts_a: &IndexMap<(usize, usize), PVar>,
        starts_b: &IndexMap<(usize, usize), PVar>,
        lens: &IndexMap<(Variable, usize), PVar>,
        candidate: &IndexMap<(usize, char), PVar>,
        subs: &SubstitutionEncoding,
        bounds: &VariableBounds,
        bound: usize,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        let mut seen = IndexSet::new();

        for (i, s) in segments_a.segments.iter().enumerate() {
            if let PatternSegment::Variable(x) = s {
                if !seen.contains(x) {
                    seen.insert(x);
                } else {
                    continue;
                }

                for pos in 0..bound {
                    for len in 0..=bounds.get(x) {
                        if pos + len < bound {
                            let var_len = as_lit(lens[&(x.clone(), len)]);
                            let startx = as_lit(starts_a[&(i, pos)]);
                            // If x starts here and has length l, then substitutions must match
                            // startx /\ len_var -> /\{c in alphabet} cand[start+k] <-> subs(x, k, c)
                            for k in 0..len {
                                for c in subs.alphabet() {
                                    let cand_sub = as_lit(candidate[&(pos + k, *c)]);
                                    let sub_var = as_lit(subs.get(x, k, *c).unwrap());
                                    clauses.push(vec![-var_len, -startx, -cand_sub, sub_var]);
                                    //clauses.push(vec![-var_len, -startx, -sub_var, cand_sub]);
                                }
                            }
                            // len + 1 must be lambda
                            if len < bounds.get(x) {
                                //let cand_sub = as_lit(candidate[&(pos + len + 1, LAMBDA)]);
                                let sub_var = as_lit(subs.get(x, len, LAMBDA).unwrap());
                                clauses.push(vec![-var_len, -startx, sub_var]);
                            }
                        } else {
                            // Cannot have this length as position
                            clauses
                                .push(vec![neg(lens[&(x.clone(), len)]), neg(starts_a[&(i, pos)])]);
                        }
                    }
                }
            }
            for (i, s) in segments_b.segments.iter().enumerate() {
                if let PatternSegment::Variable(x) = s {
                    if !seen.contains(x) {
                        seen.insert(x);
                    } else {
                        continue;
                    }

                    for pos in 0..bound {
                        for len in 0..=bounds.get(x) {
                            if pos + len < bound {
                                let var_len = as_lit(lens[&(x.clone(), len)]);
                                let startx = as_lit(starts_b[&(i, pos)]);
                                // If x starts here and has length l, then substitutions must match
                                // startx /\ len_var -> /\{c in alphabet} cand[start+k] <-> subs(x, k, c)
                                for k in 0..len {
                                    for c in subs.alphabet() {
                                        let cand_sub = as_lit(candidate[&(pos + k, *c)]);
                                        let sub_var = as_lit(subs.get(x, k, *c).unwrap());
                                        clauses.push(vec![-var_len, -startx, -cand_sub, sub_var]);
                                        //clauses.push(vec![-var_len, -startx, -sub_var, cand_sub]);
                                    }
                                }
                                // len + 1 must be lamda
                                if len < bounds.get(x) {
                                    let sub_var = as_lit(subs.get(x, len, LAMBDA).unwrap());
                                    clauses.push(vec![-var_len, -startx, sub_var]);
                                }
                            } else {
                                // Cannot have this length as position
                                clauses.push(vec![
                                    neg(lens[&(x.clone(), len)]),
                                    neg(starts_b[&(i, pos)]),
                                ]);
                            }
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }
}

impl WordEquationEncoder for BindepEncoder {
    fn new(equation: WordEquation) -> Self {
        Self {
            equation: equation,
            subs_lhs: HashMap::new(),
            subs_rhs: HashMap::new(),

            round: 0,
            bound: 0,
            last_bound: None,
            starts_lhs: IndexMap::new(),
            starts_rhs: IndexMap::new(),
            segments_lsh: None,
            segments_rhs: None,
            var_lens: IndexMap::new(),
            cand_positions: IndexMap::new(),
        }
    }
}

impl PredicateEncoder for BindepEncoder {
    fn encode(
        &mut self,
        bounds: &VariableBounds,
        substitution: &SubstitutionEncoding,
    ) -> EncodingResult {
        self.round += 1;
        let mut res = EncodingResult::empty();

        let bound = max(
            FilledPattern::fill(self.equation.lhs(), bounds).length(),
            FilledPattern::fill(self.equation.rhs(), bounds).length(),
        );

        let lhs_segs = SegmentedPattern::new(self.equation.lhs());
        let rhs_segs = SegmentedPattern::new(self.equation.rhs());

        // Encode the candidates
        let (cand_enc, cand_positions) = self.encode_candiates(bound, &self.equation.alphabet());
        log::info!("Clauses for candidates: {}", cand_enc.clauses());
        res.join(cand_enc);

        // Encode length of variables
        let (len_enc, var_lens) = self.encode_var_lenghts(&self.equation.variables(), bounds);
        log::info!("Clauses for var lengths: {}", len_enc.clauses());
        res.join(len_enc);

        // Encode alignment of segments with candidates LHS
        let (align_enc, starts_lhs) = self.encode_alignment(&lhs_segs, &var_lens, bounds, bound);
        log::info!("Clauses for alignments LHS: {}", align_enc.clauses());
        res.join(align_enc);

        // Encode alignment of segments with candidates RHS
        let (align_enc, starts_rhs) = self.encode_alignment(&rhs_segs, &var_lens, bounds, bound);
        log::info!("Clauses for alignments RHS: {}", align_enc.clauses());
        res.join(align_enc);

        // Encode matching constants LHS
        /*let const_match_enc =
            self.match_constants_candidate(&lhs_segs, &starts_lhs, &cand_positions, bound);
        log::info!(
            "Clauses for constants matching LHS: {}",
            const_match_enc.clauses()
        );
        res.join(const_match_enc);

        // Encode matching constants RHS
        let const_match_enc =
            self.match_constants_candidate(&rhs_segs, &starts_rhs, &cand_positions, bound);
        log::info!(
            "Clauses for constants matching RHS: {}",
            const_match_enc.clauses()
        );
        res.join(const_match_enc);*/

        let vars_match_lhs_enc = self.match_var_candidate(
            &lhs_segs,
            &starts_lhs,
            &cand_positions,
            &var_lens,
            substitution,
            bounds,
            bound,
        );
        log::info!(
            "Clauses for variable matching LHS: {}",
            vars_match_lhs_enc.clauses()
        );
        res.join(vars_match_lhs_enc);

        let vars_match_rhs_enc = self.match_var_candidate(
            &rhs_segs,
            &starts_rhs,
            &cand_positions,
            &var_lens,
            substitution,
            bounds,
            bound,
        );
        log::info!(
            "Clauses for variable matching RHS: {}",
            vars_match_rhs_enc.clauses()
        );
        res.join(vars_match_rhs_enc);

        let suffix_enc_lhs = self.lambda_suffix(
            &lhs_segs,
            &starts_lhs,
            &var_lens,
            &cand_positions,
            bounds,
            bound,
        );
        log::info!(
            "Clauses for lambda suffix lhs: {}",
            suffix_enc_lhs.clauses()
        );
        res.join(suffix_enc_lhs);

        let suffix_enc_rhs = self.lambda_suffix(
            &rhs_segs,
            &starts_rhs,
            &var_lens,
            &cand_positions,
            bounds,
            bound,
        );
        log::info!(
            "Clauses for lambda suffix rhs: {}",
            suffix_enc_rhs.clauses()
        );
        res.join(suffix_enc_rhs);

        // MATCHING

        /*

        // Encode matching vars
        let (match_enc, matches) =
            self.encode_match_vars(&cand_positions, &self.equation.alphabet(), bound);
        log::info!("Clauses for position matching: {}", match_enc.clauses());
        res.join(match_enc);

        // Encode matching vars LHS
        let match_inner_enc_lhs =
            self.match_vars_inner(&lhs_segs, &starts_lhs, &var_lens, &matches, bounds, bound);
        log::info!(
            "Clauses for inner matching: {}",
            match_inner_enc_lhs.clauses()
        );
        res.join(match_inner_enc_lhs);

        // Encode matching vars RHS
        let match_inner_enc_rhs =
            self.match_vars_inner(&rhs_segs, &starts_rhs, &var_lens, &matches, bounds, bound);
        log::info!(
            "Clauses for inner matching: {}",
            match_inner_enc_rhs.clauses()
        );
        res.join(match_inner_enc_rhs);

        // Encode matching vars LHS-RHS
        let match_outer_enc = self.match_vars_outer(
            &lhs_segs,
            &rhs_segs,
            &starts_lhs,
            &starts_rhs,
            &var_lens,
            &matches,
            bounds,
            bound,
        );
        log::info!("Clauses for outer matching: {}", match_outer_enc.clauses());
        res.join(match_outer_enc);

        let subs_bridge_enc = self.bridge_substitutions(
            &lhs_segs,
            &rhs_segs,
            &starts_lhs,
            &starts_rhs,
            &var_lens,
            &cand_positions,
            substitution,
            bounds,
            bound,
        );
        log::info!("Clauses for bridge subs: {}", subs_bridge_enc.clauses());
        res.join(subs_bridge_enc);
        */

        self.starts_lhs = starts_lhs;
        self.starts_rhs = starts_rhs;
        self.segments_lsh = Some(lhs_segs);
        self.segments_rhs = Some(rhs_segs);
        self.var_lens = var_lens;
        self.bound = bound;
        self.cand_positions = cand_positions;

        res
    }

    fn is_incremental(&self) -> bool {
        false
    }

    fn reset(&mut self) {
        let new = Self::new(self.equation.clone());
        // Reset everything except the equation
        *self = new;
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use cadical::Solver;

    use crate::{
        encode::substitution::SubstitutionEncoder,
        formula::Substitution,
        model::{words::Pattern, Sort, Variable},
    };

    fn solve_bindep(
        eq: &WordEquation,
        bounds: VariableBounds,
        alphabet: &IndexSet<char>,
    ) -> Option<bool> {
        let mut encoding = EncodingResult::empty();
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), eq.variables());

        let subs_cnf = subs_encoder.encode(&bounds);
        encoding.join(subs_cnf);
        let mut encoder = BindepEncoder::new(eq.clone());
        encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding().unwrap()));

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
            let solution = subs_encoder
                .get_encoding()
                .unwrap()
                .get_substitutions(&solver);
            let solution = Substitution::from(solution);
            println!("\n\n===============================================================");

            let mut w = vec![];
            for i in 0..encoder.bound {
                for c in alphabet {
                    let cvar = encoder.cand_positions[&(i, *c)];
                    if let Some(true) = solver.value(as_lit(cvar)) {
                        w.push(*c);
                    }
                }
                let cvar = encoder.cand_positions[&(i, LAMBDA)];
                if let Some(true) = solver.value(as_lit(cvar)) {
                    w.push(LAMBDA);
                }
            }
            println!("Solution word: {:?}", w);
            println!("LSH start positions:");
            for (i, s) in encoder.segments_lsh.unwrap().segments.iter().enumerate() {
                print!("\t{}", s);
                let mut spos = None;
                for pos in 0..encoder.bound {
                    let vr = encoder.starts_lhs[&(i, pos)];
                    if let Some(true) = solver.value(as_lit(vr)) {
                        assert!(spos.is_none());
                        spos = Some(pos);
                    }
                }
                assert!(spos.is_some());
                println!(": {:?}", spos.unwrap());
            }

            println!("RSH start positions:");
            for (i, s) in encoder.segments_rhs.unwrap().segments.iter().enumerate() {
                print!("\t{}", s);
                let mut spos = None;
                for pos in 0..encoder.bound {
                    let vr = encoder.starts_rhs[&(i, pos)];
                    if let Some(true) = solver.value(as_lit(vr)) {
                        assert!(spos.is_none());
                        spos = Some(pos);
                    }
                }
                assert!(spos.is_some());
                println!(": {:?}", spos.unwrap());
            }
            println!("Variable lengths:");
            for x in eq.variables() {
                let mut len = None;
                for l in 0..=bounds.get(&x) {
                    let vr = encoder.var_lens[&(x.clone(), l)];
                    if let Some(true) = solver.value(as_lit(vr)) {
                        assert!(len.is_none());
                        len = Some(l);
                    }
                }
                assert!(len.is_some());
                println!("\t{}: {:?}", x, len.unwrap());
            }
            println!("===============================================================\n\n");

            assert!(
                eq.is_solution(&solution).unwrap(),
                "{} is not a solution for {}: {:?} != {:?}",
                solution,
                eq,
                eq.lhs().substitute(&solution),
                eq.rhs().substitute(&solution)
            );
        }
        res
    }

    fn solve_bindep_incremental(
        eq: &WordEquation,
        limit: usize,
        alphabet: &IndexSet<char>,
    ) -> Option<bool> {
        let mut bounds = VariableBounds::new(1);

        let mut encoder = BindepEncoder::new(eq.clone());
        let mut subs_encoder = SubstitutionEncoder::new(alphabet.clone(), eq.variables());

        let mut result = None;
        let mut done = bounds.leq(limit);
        let mut solver: cadical::Solver = cadical::Solver::new();
        while done {
            let mut encoding = EncodingResult::empty();

            encoding.join(subs_encoder.encode(&bounds));
            encoding.join(encoder.encode(&bounds, subs_encoder.get_encoding().unwrap()));
            result = match encoding {
                EncodingResult::Cnf(cnf, assm) => {
                    for clause in cnf {
                        solver.add_clause(clause);
                    }
                    solver.solve_with(assm.into_iter())
                }
                EncodingResult::Trivial(f) => Some(f),
            };
            done = bounds.next_square(Some(limit));
        }
        match result {
            Some(true) => {
                let sol = subs_encoder
                    .get_encoding()
                    .unwrap()
                    .get_substitutions(&solver);
                let solution = Substitution::from(sol);

                assert!(
                    eq.is_solution(&solution).unwrap(),
                    "Not a solution: {} ({})",
                    solution,
                    eq
                );
            }

            _ => {}
        }
        result
    }

    #[test]
    #[ignore = "Incremental encoding is not working yet"]
    fn bindep_incremental_sat() {
        let eq = WordEquation::parse_simple("abc", "X");
        let res = solve_bindep_incremental(&eq, 10, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_empty_eq() {
        let eq = WordEquation::new(Pattern::from(vec![]), Pattern::from(vec![]));
        let bounds = VariableBounds::new(10);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_trivial_sat_consts() {
        let eq = WordEquation::constant("bar", "bar");
        let bounds = VariableBounds::new(10);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_trivial_unsat_consts() {
        let eq = WordEquation::constant("bar", "barr");
        let bounds = VariableBounds::new(10);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn bindep_trivial_sat_const_var() {
        let eq = WordEquation::new(
            Pattern::variable(&Variable::tmp_var(Sort::String)),
            Pattern::constant("bar"),
        );

        let bounds = VariableBounds::new(5);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_trivial_sat_vars() {
        let var = Pattern::variable(&Variable::tmp_var(Sort::String));
        let eq = WordEquation::new(var.clone(), var);
        let bounds = VariableBounds::new(10);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_sat_commute() {
        // AB = BA
        let var_a = Variable::tmp_var(Sort::String);
        let var_b = Variable::tmp_var(Sort::String);
        let mut lhs = Pattern::empty();
        lhs.append_var(&var_a).append_var(&var_b);
        let mut rhs = Pattern::empty();
        rhs.append_var(&var_b).append_var(&var_a);
        let eq = WordEquation::new(lhs, rhs);
        let bounds = VariableBounds::new(10);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_sat_pattern_const() {
        let eq = WordEquation::parse_simple("aXc", "abc");
        let bounds = VariableBounds::new(1);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_test() {
        let eq = WordEquation::parse_simple("aXb", "YXb");
        let bounds = VariableBounds::new(3);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_trivial_unsat_const_var_too_small() {
        let eq = WordEquation::new(
            Pattern::constant("foo"),
            Pattern::variable(&Variable::tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(1);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn bindep_sat_t1i74() {
        let eq = WordEquation::parse_simple("A", "dFg");
        let bounds = VariableBounds::new(20);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
}
