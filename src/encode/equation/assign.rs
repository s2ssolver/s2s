//! Encoder for `assignment` type equations.
//! Assignments are of the form `x = w` where `x` is a variable and `w` is a constant word.

use std::cmp::Ordering;

use crate::{
    bounds::Bounds,
    encode::{domain::DomainEncoding, ConstraintEncoder, EncodingResult, LAMBDA},
    error::Error,
    model::Variable,
    sat::{as_lit, neg, pvar},
};

pub struct AssignmentEncoder {
    lhs: Variable,
    rhs: Vec<char>,
    last_bound: Option<usize>,
    sign: bool,
}

impl AssignmentEncoder {
    pub fn new(lhs: Variable, rhs: Vec<char>, sign: bool) -> Self {
        Self {
            lhs,
            rhs,
            sign,
            last_bound: None,
        }
    }

    fn encode_eq(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let len_var = self.lhs.len_var().unwrap();
        let len_rhs = self.rhs.len();
        let bound = bounds.get_upper(&len_var).unwrap() as usize;

        let mut result = EncodingResult::empty();
        if bound < len_rhs {
            // Trivially unsatisfiable
            let p = pvar();
            result.add_clause(vec![as_lit(p)]);
            result.add_assumption(neg(p));
            return Ok(result);
        }

        let last_bound = self.last_bound.unwrap_or(0);
        // Haven't encoded anything yet, was trivially unsatisfiable in previous call
        match last_bound.cmp(&len_rhs) {
            Ordering::Less => {
                for i in 0..len_rhs {
                    let chr = self.rhs[i];
                    let sub_var = dom.string().get(&self.lhs, i, chr).unwrap();
                    result.add_clause(vec![as_lit(sub_var)]);
                }
                if bound > len_rhs {
                    // Make sure the rest of lhs is empty
                    let lambda_sub = dom.string().get(&self.lhs, len_rhs, LAMBDA).unwrap();
                    result.add_clause(vec![as_lit(lambda_sub)]);
                }
            }
            Ordering::Equal => {
                // Make sure the rest of lhs is empty, was not encoded in previous call due to bound exacly equal to rhs length
                let lambda_sub = dom.string().get(&self.lhs, len_rhs, LAMBDA).unwrap();
                result.add_clause(vec![as_lit(lambda_sub)]);
            }
            Ordering::Greater => (),
        }

        self.last_bound = Some(bound);

        Ok(result)
    }

    fn encode_ineq(
        &mut self,
        bounds: &Bounds,
        dom: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        let len_var = self.lhs.len_var().unwrap();
        let len_rhs = self.rhs.len();
        let bound = bounds.get_upper(&len_var).unwrap() as usize;

        let mut result = EncodingResult::empty();
        if bound < len_rhs {
            // Trivially satisfiable
            return Ok(result);
        }

        let last_bound = self.last_bound.unwrap_or(0);
        // Haven't encoded anything yet, was trivially unsatisfiable in previous call
        if last_bound < len_rhs {
            let mut clause = Vec::with_capacity(len_rhs);
            for i in 0..len_rhs {
                let chr = self.rhs[i];
                let sub_var = dom.string().get(&self.lhs, i, chr).unwrap();
                clause.push(neg(sub_var));
            }
            match len_rhs.cmp(&bound) {
                Ordering::Less => {
                    // lhs might also be longer than rhs
                    let lambda_sub = dom.string().get(&self.lhs, len_rhs, LAMBDA).unwrap();
                    clause.push(neg(lambda_sub));
                    result.add_clause(clause);
                }
                Ordering::Equal => {
                    // Select the clause, in next iteration we will make sure the rest of lhs can also be non-empty
                    let selector = pvar();
                    clause.push(neg(selector));
                    result.add_clause(clause);
                    result.add_assumption(as_lit(selector));
                }
                Ordering::Greater => (),
            }
        }

        self.last_bound = Some(bound);

        Ok(result)
    }
}

impl ConstraintEncoder for AssignmentEncoder {
    fn is_incremental(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Bounds,
        substitution: &DomainEncoding,
    ) -> Result<EncodingResult, Error> {
        if self.sign {
            self.encode_eq(bounds, substitution)
        } else {
            self.encode_ineq(bounds, substitution)
        }
    }
}
