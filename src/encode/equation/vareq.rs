//! Encoder for word equations of the form `x=y` where `x` and `y` are variables.

use std::{
    cmp::{min, Ordering},
    rc::Rc,
};

use crate::{
    bounds::Bounds,
    context::Variable,
    encode::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder, LAMBDA},
    sat::{nlit, plit, pvar, PVar},
};

pub struct VareqEncoder {
    last_bounds: Option<usize>,
    lhs: Rc<Variable>,
    rhs: Rc<Variable>,
    selector: Option<PVar>,
    sign: bool,
}

impl VareqEncoder {
    fn encode_eq(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        let lhs_bound = bounds.get_upper_finite(&self.lhs).unwrap() as usize;
        let rhs_bound = bounds.get_upper_finite(&self.rhs).unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);

        let last_bound = self.last_bounds.unwrap_or(0);
        assert!(next_bound >= last_bound);

        let alph = dom.alphabet();
        let mut res = EncodingResult::empty();
        for pos in last_bound..next_bound {
            for c in alph.iter() {
                let lhs_pos_c = dom.string().get_sub(&self.lhs, pos, c).unwrap();
                let rhs_pos_c = dom.string().get_sub(&self.rhs, pos, c).unwrap();
                let clause = vec![nlit(lhs_pos_c), plit(rhs_pos_c)];
                res.add_clause(clause);
            }
            let lhs_pos_c = dom.string().get_sub(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom.string().get_sub(&self.rhs, pos, LAMBDA).unwrap();
            let clause = vec![nlit(lhs_pos_c), plit(rhs_pos_c)];
            res.add_clause(clause);
        }

        // Make sure the rest of the longer string is empty
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom.string().get_sub(&self.rhs, next_bound, LAMBDA).unwrap();
                res.add_assumption(plit(rhs_lambda))
            }
            Ordering::Greater => {
                let lhs_lambda = dom.string().get_sub(&self.lhs, next_bound, LAMBDA).unwrap();
                res.add_assumption(plit(lhs_lambda))
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
    ) -> Result<EncodingResult, EncodingError> {
        let lhs_bound = bounds.get_upper_finite(&self.lhs).unwrap() as usize;
        let rhs_bound = bounds.get_upper_finite(&self.rhs).unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);
        if let Some(b) = self.last_bounds {
            assert!(next_bound >= b);

            if b == next_bound {
                // Just return the same assumption again, the encoding stays the same
                if let Some(a) = self.selector {
                    let mut res = EncodingResult::empty();
                    res.add_assumption(plit(a));
                    return Ok(res);
                }
            }
        }

        let alph = dom.alphabet();
        let mut res = EncodingResult::empty();

        // Deactivate selector from last iteration and create a new one
        if let Some(s) = self.selector {
            res.add_clause(vec![nlit(s)]);
        }
        let selector = pvar();
        self.selector = Some(selector);

        let mut def_clause = vec![nlit(selector)];
        res.add_assumption(plit(selector));
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom.string().get_sub(&self.rhs, next_bound, LAMBDA).unwrap();
                def_clause.push(nlit(rhs_lambda));
            }
            Ordering::Greater => {
                let lhs_lambda = dom.string().get_sub(&self.lhs, next_bound, LAMBDA).unwrap();
                def_clause.push(nlit(lhs_lambda));
            }
            _ => (),
        }

        for pos in 0..next_bound {
            for c in alph.iter() {
                let p = pvar();
                def_clause.push(plit(p));
                let lhs_pos_c = dom.string().get_sub(&self.lhs, pos, c).unwrap();
                let rhs_pos_c = dom.string().get_sub(&self.rhs, pos, c).unwrap();

                // p --> (-h(x[pos]) = a /\ h(y[pos]) = a)
                // <==> (-p \/ -h(x[pos]) = a) /\ (-p \/ h(y[pos]) = a)
                let clause_lhs = vec![nlit(p), nlit(lhs_pos_c)];
                let clause_rhs = vec![nlit(p), plit(rhs_pos_c)];
                res.add_clause(clause_lhs);
                res.add_clause(clause_rhs);

                // (-h(x[pos]) = a /\ h(y[pos]) = a) --> p
                // <==> (h(x[pos]) = a \/ -h(y[pos]) = a \/ p)
                let clause = vec![plit(lhs_pos_c), nlit(rhs_pos_c), plit(p)];
                res.add_clause(clause);
            }
            // Repeat for lambda
            let p = pvar();
            let lhs_pos_c = dom.string().get_sub(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom.string().get_sub(&self.rhs, pos, LAMBDA).unwrap();
            let clause_lhs = vec![nlit(p), nlit(lhs_pos_c)];
            let clause_rhs = vec![nlit(p), plit(rhs_pos_c)];
            res.add_clause(clause_lhs);
            res.add_clause(clause_rhs);
            let clause = vec![plit(lhs_pos_c), nlit(rhs_pos_c), plit(p)];

            res.add_clause(clause);
        }
        res.add_clause(def_clause);
        self.last_bounds = Some(next_bound);

        Ok(res)
    }

    pub fn new(lhs: &Rc<Variable>, rhs: &Rc<Variable>, sign: bool) -> Self {
        Self {
            last_bounds: None,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            selector: None,
            sign,
        }
    }
}

impl LiteralEncoder for VareqEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.sign {
            self.encode_eq(bounds, dom)
        } else {
            self.encode_ineq(bounds, dom)
        }
    }
}
