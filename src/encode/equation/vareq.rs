//! Encoder for word equations of the form `x=y` where `x` and `y` are variables.

use std::cmp::{min, Ordering};

use crate::{
    bounds::Bounds,
    encode::{domain::DomainEncoding, ConstraintEncoder, EncodingResult, LAMBDA},
    error::Error,
    model::Variable,
    sat::{as_lit, neg, pvar, PVar},
};

pub struct VareqEncoder {
    last_bounds: Option<usize>,
    lhs: Variable,
    rhs: Variable,
    selector: Option<PVar>,
    sign: bool,
}

impl VareqEncoder {
    fn encode_eq(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let lhs_len = self.lhs.len_var().unwrap();
        let rhs_len = self.rhs.len_var().unwrap();

        let lhs_bound = bounds.get_upper(&lhs_len).unwrap() as usize;
        let rhs_bound = bounds.get_upper(&rhs_len).unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);

        let last_bound = self.last_bounds.unwrap_or(0);
        assert!(next_bound >= last_bound);

        let alph = dom.alphabet();
        let mut res = EncodingResult::empty();
        for pos in last_bound..next_bound {
            for c in alph {
                let lhs_pos_c = dom.string().get(&self.lhs, pos, *c).unwrap();
                let rhs_pos_c = dom.string().get(&self.rhs, pos, *c).unwrap();
                let clause = vec![neg(lhs_pos_c), as_lit(rhs_pos_c)];
                res.add_clause(clause);
            }
            let lhs_pos_c = dom.string().get(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom.string().get(&self.rhs, pos, LAMBDA).unwrap();
            let clause = vec![neg(lhs_pos_c), as_lit(rhs_pos_c)];
            res.add_clause(clause);
        }

        // Make sure the rest of the longer string is empty
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom.string().get(&self.rhs, next_bound, LAMBDA).unwrap();
                res.add_assumption(as_lit(rhs_lambda))
            }
            Ordering::Greater => {
                let lhs_lambda = dom.string().get(&self.lhs, next_bound, LAMBDA).unwrap();
                res.add_assumption(as_lit(lhs_lambda))
            }
            _ => (),
        }

        self.last_bounds = Some(next_bound);
        Ok(res)
    }

    fn encode_ineq(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let lhs_len = self.lhs.len_var().unwrap();
        let rhs_len = self.rhs.len_var().unwrap();

        let lhs_bound = bounds.get_upper(&lhs_len).unwrap() as usize;
        let rhs_bound = bounds.get_upper(&rhs_len).unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);
        if let Some(b) = self.last_bounds {
            assert!(next_bound >= b);

            if b == next_bound {
                // Just return the same assumption again, the encoding stays the same
                if let Some(a) = self.selector {
                    let mut res = EncodingResult::empty();
                    res.add_assumption(as_lit(a));
                    return Ok(res);
                }
            }
        }

        let alph = dom.alphabet();
        let mut res = EncodingResult::empty();

        // Deactivate selector from last iteration and create a new one
        if let Some(s) = self.selector {
            res.add_clause(vec![neg(s)]);
        }
        let selector = pvar();
        self.selector = Some(selector);

        let mut def_clause = vec![neg(selector)];
        res.add_assumption(as_lit(selector));
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom.string().get(&self.rhs, next_bound, LAMBDA).unwrap();
                def_clause.push(neg(rhs_lambda));
            }
            Ordering::Greater => {
                let lhs_lambda = dom.string().get(&self.lhs, next_bound, LAMBDA).unwrap();
                def_clause.push(neg(lhs_lambda));
            }
            _ => (),
        }

        for pos in 0..next_bound {
            for c in alph {
                let p = pvar();
                def_clause.push(as_lit(p));
                let lhs_pos_c = dom.string().get(&self.lhs, pos, *c).unwrap();
                let rhs_pos_c = dom.string().get(&self.rhs, pos, *c).unwrap();

                // p --> (-h(x[pos]) = a /\ h(y[pos]) = a)
                // <==> (-p \/ -h(x[pos]) = a) /\ (-p \/ h(y[pos]) = a)
                let clause_lhs = vec![neg(p), neg(lhs_pos_c)];
                let clause_rhs = vec![neg(p), as_lit(rhs_pos_c)];
                res.add_clause(clause_lhs);
                res.add_clause(clause_rhs);

                // (-h(x[pos]) = a /\ h(y[pos]) = a) --> p
                // <==> (h(x[pos]) = a \/ -h(y[pos]) = a \/ p)
                let clause = vec![as_lit(lhs_pos_c), neg(rhs_pos_c), as_lit(p)];
                res.add_clause(clause);
            }
            // Repeat for lambda
            let p = pvar();
            let lhs_pos_c = dom.string().get(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom.string().get(&self.rhs, pos, LAMBDA).unwrap();
            let clause_lhs = vec![neg(p), neg(lhs_pos_c)];
            let clause_rhs = vec![neg(p), as_lit(rhs_pos_c)];
            res.add_clause(clause_lhs);
            res.add_clause(clause_rhs);
            let clause = vec![as_lit(lhs_pos_c), neg(rhs_pos_c), as_lit(p)];

            res.add_clause(clause);
        }
        res.add_clause(def_clause);
        self.last_bounds = Some(next_bound);

        Ok(res)
    }

    pub fn new(lhs: &Variable, rhs: &Variable, sign: bool) -> Self {
        Self {
            last_bounds: None,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            selector: None,
            sign,
        }
    }
}

impl ConstraintEncoder for VareqEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(&mut self, bounds: &Bounds, dom: &DomainEncoding) -> Result<EncodingResult, Error> {
        if self.sign {
            self.encode_eq(bounds, dom)
        } else {
            self.encode_ineq(bounds, dom)
        }
    }
}
