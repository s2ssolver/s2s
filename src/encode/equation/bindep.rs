use std::cmp::max;

use std::fmt::Display;
use std::time::Instant;

use crate::encode::card::{exactly_one, IncrementalAMO};
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

    fn suffix_len(&self, i: usize) -> usize {
        let mut f = 0;
        for j in i + 1..self.length() {
            if let PatternSegment::Word(w) = self.get(j) {
                f += w.len();
            }
        }
        f
    }

    fn iter(&self) -> impl Iterator<Item = &PatternSegment> {
        self.segments.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum EqSide {
    Lhs,
    Rhs,
}

impl Display for EqSide {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EqSide::Lhs => write!(f, "LHS"),
            EqSide::Rhs => write!(f, "RHS"),
        }
    }
}

pub struct BindepEncoder {
    /// The original word equation
    equation: WordEquation,

    /// Upper bound for the solution word, is 0 prior to first round.
    bound: usize,

    /// The last bound that was used, is `None` prior to the first round.
    last_bound: Option<usize>,

    /// A Boolean variable that is added as an assumption to the SAT solver for the current upper bound.
    /// The negation of this variable is added as an assumption at the next upper bound.
    bound_selector: Option<PVar>,

    /// The variable bounds used in the last round.
    /// Is `None` in the first round.
    last_var_bounds: Option<VariableBounds>,

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

    /// The encoding of the candidate solution word. Maps pairs of positions and characters to a propositional variable that is true if the character is at the position.
    cand_positions: IndexMap<(usize, char), PVar>,

    /// Maps each segment index to and incremental at-most-one encoder that is used to encode the possible start positions of the segment.
    segs_starts_amo: IndexMap<(EqSide, usize), IncrementalAMO>,

    /// The variable-solution matching variables.
    var_matches: IndexMap<(Variable, usize, usize), PVar>,

    var_cand_match_cache: IndexMap<(Variable, usize, usize), PVar>,

    /// The alphabet
    alphabet: IndexSet<char>,
}

impl BindepEncoder {
    /// Returns the Boolean variable that is true if the character is at the position in the candidate solution word.
    fn candidate_at(&self, pos: usize, c: char) -> PVar {
        self.cand_positions[&(pos, c)]
    }

    fn segments(&self, side: &EqSide) -> &SegmentedPattern {
        match side {
            EqSide::Lhs => &self.segments_lsh,
            EqSide::Rhs => &self.segments_rhs,
        }
    }

    /// Sets the Boolean variable that is true if the character is at the position in the candidate solution word.
    /// Panics if the variable was already set.
    fn set_candidate_at(&mut self, pos: usize, c: char, var: PVar) {
        let res = self.cand_positions.insert((pos, c), var);
        assert!(res.is_none());
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

    /// Returns the variables' bound used in the last round.
    /// Returns None prior to the first round.
    fn get_last_var_bound(&self, var: &Variable) -> Option<usize> {
        self.last_var_bounds.as_ref().map(|bounds| bounds.get(var))
    }

    /// Encodes the possible candidates for the solution word up to bound `self.bound`.
    fn encode_candidates(&mut self) -> EncodingResult {
        let mut res = EncodingResult::empty();
        let last_bound = self.last_bound.unwrap_or(0);
        for pos in last_bound..self.bound {
            let mut p_choices = vec![];
            for c in self.alphabet.clone() {
                let v = pvar();
                p_choices.push(v);
                self.set_candidate_at(pos, c, v);
            }
            let v_lambda = pvar();
            p_choices.push(v_lambda);
            self.set_candidate_at(pos, LAMBDA, v_lambda);

            let cnf = exactly_one(&p_choices);
            res.join(EncodingResult::cnf(cnf));

            // If a position is lambda, then only lambda may follow
            if pos > 0 {
                let last_lambda = self.candidate_at(pos - 1, LAMBDA);
                res.join(EncodingResult::cnf(vec![vec![
                    neg(last_lambda),
                    as_lit(v_lambda),
                ]]));
            }
        }
        res
    }

    /// Encodes the alignment of a segmented pattern with the solution word by matching the respective lengths.
    fn encode_alignment(
        &mut self,
        bounds: &VariableBounds,
        side: &EqSide,
        subs: &SubstitutionEncoding,
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
            let amo = self
                .segs_starts_amo
                .entry((side.clone(), i))
                .or_default()
                .add(&starts_i);
            res.join(amo);
        }

        // Encode start position needs to be 0 for the first segment
        for pos in last_bound..self.bound {
            let var = self.start_position(0, pos, side);
            if pos == 0 {
                // Segment 0 must start at position 0, and at no other position
                res.add_clause(vec![as_lit(var)]);
            } else {
                res.add_clause(vec![neg(var)]);
            }
        }

        for (i, s) in segments.iter().enumerate() {
            if i == n_seg - 1 {
                // Last segment does not have a successor
                continue;
            }

            // Disable all starts that are too early
            for p in last_bound..segments.earliest_start(i) {
                let var = self.start_position(i, p, side);
                res.add_clause(vec![neg(var)]);
            }

            match s {
                PatternSegment::Variable(v) => {
                    let start_pos = segments.earliest_start(i);
                    // Incremental either: Length is longer OR start position is later OR Both
                    for pos in start_pos..self.bound {
                        // TODO: Put all "disabled" start-length-pairs is a list and process on next iteration instead of iterating over all pairs and checking the condition
                        let last_vbound = self.get_last_var_bound(v).unwrap_or(0);
                        let vbound = bounds.get(v);

                        for len in 0..=vbound {
                            // Start position of next segment is i+len
                            let len_var = subs.get_len(v, len).unwrap();
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            let svar = self.start_position(i, pos, side);

                            // If pos < self.last_bound AND len <= last_vbound, then we already encoded this.
                            // Check if any of the previously invalid position/length pairs became valid
                            if pos < last_bound && len <= last_vbound {
                                if pos + len
                                    >= last_bound - (segments.suffix_len(i).saturating_sub(1))
                                {
                                    if pos + len
                                        < self.bound - (segments.suffix_len(i).saturating_sub(1))
                                    {
                                        // These length/position combinations is now possible

                                        let succ = self.start_position(i + 1, pos + len, side);

                                        res.add_clause(vec![neg(svar), neg(len_var), as_lit(succ)]);
                                    } else {
                                        // Still not viable, disable again
                                        let selector = self.bound_selector.unwrap();
                                        res.add_clause(vec![
                                            neg(selector),
                                            neg(svar),
                                            neg(len_var),
                                        ]);
                                    }
                                }
                                continue;
                            }

                            // Encode alignment for new position/length pairs
                            if pos + len < self.bound - (segments.suffix_len(i).saturating_sub(1)) {
                                let succ = self.start_position(i + 1, pos + len, side);

                                res.add_clause(vec![neg(svar), neg(len_var), as_lit(succ)]);
                            } else {
                                // Cannot start here with length l with current bound
                                let selector = self.bound_selector.unwrap();
                                res.add_clause(vec![neg(selector), neg(svar), neg(len_var)]);
                            }
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    // Only consider the new possible starting positions
                    for pos in segments.earliest_start(i)..self.bound {
                        let len = w.len();
                        let svar = self.start_position(i, pos, side);
                        // Already considered last round
                        if pos < last_bound {
                            // Extends over the last bound, but not over the current bound
                            if pos + len >= last_bound - segments.suffix_len(i) {
                                // This position was disabled for last bound, but now became viable
                                if pos + len < self.bound - segments.suffix_len(i) {
                                    let succ = self.start_position(i + 1, pos + len, side);
                                    res.add_clause(vec![neg(svar), as_lit(succ)]);
                                } else {
                                    // Still not viable, disable again
                                    res.add_assumption(neg(svar));
                                }
                            }
                            // Does not extend over the last bound, so we already encoded it and can continue
                            continue;
                        }
                        if pos + len < self.bound - segments.suffix_len(i) {
                            // S_i^p /\ len_var -> S_{i+1}^(p+len)
                            let succ = self.start_position(i + 1, pos + len, side);
                            res.add_clause(vec![neg(svar), as_lit(succ)]);
                        } else {
                            // Cannot start here. Deactivate by means of an assumption, as we might be able to activate it later, when the bound increases
                            res.add_assumption(neg(svar));
                        }
                    }
                }
            }
        }

        res
    }

    fn match_candidate(
        &mut self,
        subs: &SubstitutionEncoding,
        bounds: &VariableBounds,
        side: &EqSide,
    ) -> EncodingResult {
        let mut clauses = Cnf::new();
        // Need to clone due to mutable borrow later
        let segments = self.segments(side).clone();

        let last_bound = self.last_bound.unwrap_or(0);
        for (i, s) in segments.iter().enumerate() {
            match s {
                PatternSegment::Variable(x) => {
                    for l in 0..=bounds.get(x) {
                        let len_var = subs.get_len(x, l).unwrap();
                        for p in segments.earliest_start(i)..self.bound {
                            let start_var = self.start_position(i, p, side);
                            if p < last_bound
                                && l < self.get_last_var_bound(x).unwrap_or(0)
                                && l + p < last_bound.saturating_sub(segments.suffix_len(i))
                            {
                                // Already encoded
                                continue;
                            }
                            if l + p <= self.bound - segments.suffix_len(i) {
                                // If segment starts here, then the next |w| positions must match substitution of x
                                match l {
                                    1 => {
                                        let m_var: u32 = pvar();
                                        self.var_matches.insert((x.clone(), p, l), m_var);
                                        for c in subs.alphabet() {
                                            let cand_c = self.candidate_at(p, *c);
                                            let sub_c = subs.get(x, 0, *c).unwrap();
                                            clauses.push(vec![
                                                neg(m_var),
                                                neg(cand_c),
                                                as_lit(sub_c),
                                            ]);
                                            clauses.push(vec![
                                                neg(m_var),
                                                as_lit(cand_c),
                                                neg(sub_c),
                                            ]);
                                        }
                                        clauses.push(vec![
                                            neg(start_var),
                                            neg(len_var),
                                            as_lit(m_var),
                                        ]);
                                    }
                                    n if n > 1 => {
                                        let m_var = pvar();
                                        let pred_m_var = self.var_matches[&(x.clone(), p, l - 1)];
                                        clauses.push(vec![neg(m_var), as_lit(pred_m_var)]);
                                        self.var_matches.insert((x.clone(), p, l), m_var);
                                        // Cache this with variable
                                        // I.e., match(x[l-1], cand[p+l-1]) -> EX c. such that they match
                                        let mv = match self.var_cand_match_cache.get(&(
                                            x.clone(),
                                            l - 1,
                                            p + (l - 1),
                                        )) {
                                            Some(mv) => {
                                                // println!("HIT");
                                                *mv
                                            }
                                            None => {
                                                let mv = pvar();
                                                for c in subs.alphabet() {
                                                    let cand_c = self.candidate_at(p + (l - 1), *c);
                                                    let sub_c = subs.get(x, l - 1, *c).unwrap();
                                                    clauses.push(vec![
                                                        neg(mv),
                                                        neg(cand_c),
                                                        as_lit(sub_c),
                                                    ]);
                                                    clauses.push(vec![
                                                        neg(mv),
                                                        as_lit(cand_c),
                                                        neg(sub_c),
                                                    ]);
                                                }
                                                mv
                                            }
                                        };
                                        self.var_cand_match_cache
                                            .insert((x.clone(), l - 1, p + (l - 1)), mv);
                                        clauses.push(vec![neg(m_var), as_lit(mv)]);

                                        clauses.push(vec![
                                            neg(start_var),
                                            neg(len_var),
                                            as_lit(m_var),
                                        ]);
                                    }
                                    _ => {}
                                }
                            }
                        }
                        // Next position in variable, if exists, is lambda
                        if self.get_last_var_bound(x).unwrap_or(0) <= l && l < bounds.get(x) {
                            // If variable is assigned length l, then the position x[l] (and implicitly all following) must be lambda
                            let sub_lambda = subs.get(x, l, LAMBDA).unwrap();

                            clauses.push(vec![neg(len_var), as_lit(sub_lambda)]);
                        }
                    }
                }
                PatternSegment::Word(w) => {
                    for p in segments.earliest_start(i)
                        ..self.bound - (w.len() - 1) - segments.suffix_len(i)
                    {
                        if p < last_bound && p < last_bound - (w.len() - 1) - segments.suffix_len(i)
                        {
                            // Already encoded
                            continue;
                        }

                        let start_var = self.start_position(i, p, side);
                        // If segment starts here, then the next |w| positions must match w
                        // S_i^p  -> /\{k=0...|w|} c_{p+j} = w[k]

                        for (k, c) in w.iter().enumerate() {
                            let cand_var = self.candidate_at(p + k, *c);
                            clauses.push(vec![neg(start_var), as_lit(cand_var)]);
                        }
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }

    fn lambda_suffix(
        &self,
        bounds: &VariableBounds,
        side: &EqSide,
        subs: &SubstitutionEncoding,
    ) -> EncodingResult {
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
                    for l in 0..=bounds.get(x) {
                        // Filter out l,p pairs that have been encoded already, i.e. p+l < last_bound
                        if p < last_bound
                            && l < self.get_last_var_bound(x).unwrap_or(0)
                            && p + l < last_bound
                        {
                            continue;
                        }
                        if p + l < self.bound {
                            let start_var = self.start_position(last, p, side);
                            let len_var = subs.get_len(x, l).unwrap();
                            let cand_var = self.candidate_at(p + l, LAMBDA);

                            clauses.push(vec![neg(start_var), neg(len_var), as_lit(cand_var)]);
                        }
                    }
                }
            }
            PatternSegment::Word(w) => {
                for p in 0..self.bound {
                    // 🔧 Skip p which are already encoded, i.e., skip p with p+w.len() < last_bound

                    if p + w.len() >= last_bound && p + w.len() < self.bound {
                        let start_var = self.start_position(last, p, side);
                        let cand_var = self.candidate_at(p + w.len(), LAMBDA);
                        clauses.push(vec![neg(start_var), as_lit(cand_var)]);
                    }
                }
            }
        }
        EncodingResult::cnf(clauses)
    }
}

impl WordEquationEncoder for BindepEncoder {
    fn new(equation: WordEquation) -> Self {
        let lhs_segs = SegmentedPattern::new(equation.lhs());
        let rhs_segs = SegmentedPattern::new(equation.rhs());
        let alph = equation.alphabet();
        Self {
            equation,
            bound_selector: None,
            round: 0,
            bound: 0,
            last_bound: None,
            last_var_bounds: None,
            alphabet: alph,
            starts_lhs: IndexMap::new(),
            starts_rhs: IndexMap::new(),
            segs_starts_amo: IndexMap::new(),
            segments_lsh: lhs_segs,
            segments_rhs: rhs_segs,
            var_cand_match_cache: IndexMap::new(),
            cand_positions: IndexMap::new(),
            var_matches: IndexMap::new(),
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
        assert!(bound >= self.bound, "Bound cannot shrink");

        // Todo: If the bound stays the same, the previous rounds' encoding is still correct.
        // In this case, we need to return the same set of assumptions.

        if let Some(v) = self.bound_selector {
            // Deactivate all clauses that were only valid for the previous bound
            res.join(EncodingResult::cnf(vec![vec![neg(v)]]));
        }
        self.bound = bound;

        // New selector for this round
        self.bound_selector = Some(pvar());

        // Encode the candidates
        let cand_enc = self.encode_candidates();
        log::debug!("Clauses for candidates: {}", cand_enc.clauses());
        res.join(cand_enc);

        // Encode alignment of segments with candidates LHS
        let ts = Instant::now();
        let align_enc = self.encode_alignment(bounds, &EqSide::Lhs, substitution);
        log::debug!(
            "Clauses for alignments LHS: {} ({} ms)",
            align_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.join(align_enc);

        // Encode alignment of segments with candidates RHS
        let ts = Instant::now();
        let align_enc = self.encode_alignment(bounds, &EqSide::Rhs, substitution);
        log::debug!(
            "Clauses for alignments RHS: {} ({} ms)",
            align_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.join(align_enc);

        let ts = Instant::now();
        let vars_match_lhs_enc = self.match_candidate(substitution, bounds, &EqSide::Lhs);
        log::debug!(
            "Clauses for variable matching LHS: {} ({} ms)",
            vars_match_lhs_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.join(vars_match_lhs_enc);

        let ts = Instant::now();
        let vars_match_rhs_enc = self.match_candidate(substitution, bounds, &EqSide::Rhs);
        log::debug!(
            "Clauses for variable matching RHS: {} ({} ms)",
            vars_match_rhs_enc.clauses(),
            ts.elapsed().as_millis()
        );
        res.join(vars_match_rhs_enc);

        let suffix_enc_lhs = self.lambda_suffix(bounds, &EqSide::Lhs, substitution);
        log::debug!(
            "Clauses for lambda suffix lhs: {}",
            suffix_enc_lhs.clauses()
        );
        res.join(suffix_enc_lhs);

        let suffix_enc_rhs = self.lambda_suffix(bounds, &EqSide::Rhs, substitution);
        log::debug!(
            "Clauses for lambda suffix rhs: {}",
            suffix_enc_rhs.clauses()
        );
        res.join(suffix_enc_rhs);

        // Store variable bounds for next round
        self.last_var_bounds = Some(bounds.clone());
        self.last_bound = Some(self.bound);
        res
    }

    fn is_incremental(&self) -> bool {
        true
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
        model::{words::Pattern, Sort, VarManager, Variable},
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
            for (i, s) in encoder.segments_lsh.segments.iter().enumerate() {
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
            for (i, s) in encoder.segments_rhs.segments.iter().enumerate() {
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
                    let vr = subs_encoder.get_encoding().unwrap().get_len(&x, l).unwrap();
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
                for (i, s) in encoder.segments_lsh.segments.iter().enumerate() {
                    print!("\t{}", s);
                    let mut spos = None;
                    for pos in 0..encoder.bound {
                        let vr = encoder.starts_lhs[&(i, pos)];
                        if let Some(true) = solver.value(as_lit(vr)) {
                            assert!(spos.is_none());
                            spos = Some(pos);
                        }
                    }
                    //assert!(spos.is_some());
                    println!(": {:?}", spos);
                }

                println!("RSH start positions:");
                for (i, s) in encoder.segments_rhs.segments.iter().enumerate() {
                    print!("\t{}", s);
                    let mut spos = None;
                    for pos in 0..encoder.bound {
                        let vr = encoder.starts_rhs[&(i, pos)];
                        if let Some(true) = solver.value(as_lit(vr)) {
                            assert!(spos.is_none());
                            spos = Some(pos);
                        }
                    }
                    //assert!(spos.is_some());
                    println!(": {:?}", spos);
                }
                println!("Variable lengths:");
                for x in eq.variables() {
                    let mut len: Option<(usize, u32)> = None;
                    for l in 0..=bounds.get(&x) {
                        let vr = subs_encoder.get_encoding().unwrap().get_len(&x, l).unwrap();
                        if let Some(true) = solver.value(as_lit(vr)) {
                            assert!(
                                len.is_none(),
                                "Variable {} has multiple lengths: {} and {}",
                                x,
                                len.unwrap().0,
                                l
                            );
                            len = Some((l, vr));
                        }
                    }
                    assert!(len.is_some());
                    println!("\t{}: {} (Var {})", x, len.unwrap().0, len.unwrap().1);
                }
                println!("===============================================================\n\n");
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
    //#[ignore = "Incremental encoding is not working yet"]
    fn bindep_incremental_sat() {
        let eq = WordEquation::parse_simple("abc", "X");
        let res = solve_bindep_incremental(&eq, 5, &eq.alphabet());
        //let bounds = VariableBounds::new(10);
        //let res = solve_bindep(&eq, bounds, &eq.alphabet());
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
        let mut vm = VarManager::new();
        let eq = WordEquation::new(
            Pattern::variable(&vm.tmp_var(Sort::String)),
            Pattern::constant("bar"),
        );

        let bounds = VariableBounds::new(5);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_trivial_sat_vars() {
        let mut vm = VarManager::new();
        let var = Pattern::variable(&vm.tmp_var(Sort::String));
        let eq = WordEquation::new(var.clone(), var);
        let bounds = VariableBounds::new(10);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_sat_commute() {
        let mut vm = VarManager::new();
        // AB = BA
        let var_a = vm.tmp_var(Sort::String);
        let var_b = vm.tmp_var(Sort::String);
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
        let mut vm = VarManager::new();
        let eq = WordEquation::new(
            Pattern::constant("foo"),
            Pattern::variable(&vm.tmp_var(Sort::String)),
        );

        let bounds = VariableBounds::new(1);

        let res = solve_bindep(&eq, bounds, &eq.alphabet());
        assert!(matches!(res, Some(false)));
    }

    #[test]
    fn bindep_sat_t1i74() {
        let eq = WordEquation::parse_simple("A", "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd");
        let bounds = VariableBounds::new(50);
        let res = solve_bindep(&eq, bounds, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
    #[test]
    fn bindep_sat_t1i74_incremental() {
        let eq = WordEquation::parse_simple("A", "ebcaeccedbedefbfdFgbagebcbfacgadbefcffcgceeedd");

        let res = solve_bindep_incremental(&eq, 50, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_sat_t1i1() {
        let eq = WordEquation::parse_simple(
            "cfcbbAadeeaecAgebegeecafegebdbagddaadbddcaeeebfabfefabfacdgAgaabg",
            "AfcbbAaIegeeAaD",
        );
        let res = solve_bindep_incremental(&eq, 50, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }

    #[test]
    fn bindep_sat_t1i97() {
        let eq = WordEquation::parse_simple("AccAbccB", "CccAbDbcCcA");
        let res = solve_bindep_incremental(&eq, 50, &eq.alphabet());

        assert!(matches!(res, Some(true)));
    }
}
