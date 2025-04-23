//! Encoder for word equations of the form `x=y` where `x` and `y` are variables.

use std::{
    cmp::{min, Ordering},
    rc::Rc,
};

use rustsat::clause;

use crate::{
    context::Variable,
    domain::Domain,
    encode::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink, LAMBDA},
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
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let lhs_bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;
        let rhs_bound = dom
            .get_string(&self.rhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);

        let last_bound = self.last_bounds.unwrap_or(0);
        assert!(next_bound >= last_bound);

        let alph = dom_enc.alphabet();

        for pos in last_bound..next_bound {
            for c in alph.iter() {
                let lhs_pos_c = dom_enc.string().get_sub(&self.lhs, pos, c).unwrap();
                let rhs_pos_c = dom_enc.string().get_sub(&self.rhs, pos, c).unwrap();
                let clause = clause![nlit(lhs_pos_c), plit(rhs_pos_c)];
                sink.add_clause(clause);
            }
            let lhs_pos_c = dom_enc.string().get_sub(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom_enc.string().get_sub(&self.rhs, pos, LAMBDA).unwrap();
            let clause = clause![nlit(lhs_pos_c), plit(rhs_pos_c)];
            sink.add_clause(clause);
        }

        // Make sure the rest of the longer string is empty
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom_enc
                    .string()
                    .get_sub(&self.rhs, next_bound, LAMBDA)
                    .unwrap();
                sink.add_assumption(plit(rhs_lambda))
            }
            Ordering::Greater => {
                let lhs_lambda = dom_enc
                    .string()
                    .get_sub(&self.lhs, next_bound, LAMBDA)
                    .unwrap();
                sink.add_assumption(plit(lhs_lambda))
            }
            _ => (),
        }

        self.last_bounds = Some(next_bound);
        Ok(())
    }

    fn encode_ineq(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let lhs_bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;
        let rhs_bound = dom
            .get_string(&self.rhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;
        let next_bound = min(lhs_bound, rhs_bound);
        if let Some(b) = self.last_bounds {
            assert!(next_bound >= b);

            if b == next_bound {
                // Just return the same assumption again, the encoding stays the same
                if let Some(a) = self.selector {
                    sink.add_assumption(plit(a));
                    return Ok(());
                }
            }
        }

        let alph = dom_enc.alphabet();

        // Deactivate selector from last iteration and create a new one
        if let Some(s) = self.selector {
            sink.add_clause(clause![nlit(s)]);
        }
        let selector = pvar();
        self.selector = Some(selector);

        let mut def_clause = clause![nlit(selector)];
        sink.add_assumption(plit(selector));
        match lhs_bound.cmp(&rhs_bound) {
            Ordering::Less => {
                let rhs_lambda = dom_enc
                    .string()
                    .get_sub(&self.rhs, next_bound, LAMBDA)
                    .unwrap();
                def_clause.add(nlit(rhs_lambda));
            }
            Ordering::Greater => {
                let lhs_lambda = dom_enc
                    .string()
                    .get_sub(&self.lhs, next_bound, LAMBDA)
                    .unwrap();
                def_clause.add(nlit(lhs_lambda));
            }
            _ => (),
        }

        for pos in 0..next_bound {
            for c in alph.iter() {
                let p = pvar();
                def_clause.add(plit(p));
                let lhs_pos_c = dom_enc.string().get_sub(&self.lhs, pos, c).unwrap();
                let rhs_pos_c = dom_enc.string().get_sub(&self.rhs, pos, c).unwrap();

                // p --> (-h(x[pos]) = a /\ h(y[pos]) = a)
                // <==> (-p \/ -h(x[pos]) = a) /\ (-p \/ h(y[pos]) = a)
                let clause_lhs = clause![nlit(p), nlit(lhs_pos_c)];
                let clause_rhs = clause![nlit(p), plit(rhs_pos_c)];
                sink.add_clause(clause_lhs);
                sink.add_clause(clause_rhs);

                // (-h(x[pos]) = a /\ h(y[pos]) = a) --> p
                // <==> (h(x[pos]) = a \/ -h(y[pos]) = a \/ p)
                let clause = clause![plit(lhs_pos_c), nlit(rhs_pos_c), plit(p)];
                sink.add_clause(clause);
            }
            // Repeat for lambda
            let p = pvar();
            let lhs_pos_c = dom_enc.string().get_sub(&self.lhs, pos, LAMBDA).unwrap();
            let rhs_pos_c = dom_enc.string().get_sub(&self.rhs, pos, LAMBDA).unwrap();
            let clause_lhs = clause![nlit(p), nlit(lhs_pos_c)];
            let clause_rhs = clause![nlit(p), plit(rhs_pos_c)];
            sink.add_clause(clause_lhs);
            sink.add_clause(clause_rhs);
            let clause = clause![plit(lhs_pos_c), nlit(rhs_pos_c), plit(p)];

            sink.add_clause(clause);
        }
        sink.add_clause(def_clause);
        self.last_bounds = Some(next_bound);

        Ok(())
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

impl EncodeLiteral for VareqEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Domain,
        dom: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        if self.sign {
            self.encode_eq(bounds, dom, sink)
        } else {
            self.encode_ineq(bounds, dom, sink)
        }
    }
}
