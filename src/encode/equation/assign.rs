//! Encoder for `assignment` type equations.
//! Assignments are of the form `x = w` where `x` is a variable and `w` is a constant word.

use std::{cmp::Ordering, rc::Rc};

use smtlib_str::SmtString;

use crate::{
    domain::Domain,
    encode::{domain::DomainEncoding, EncodingError, EncodingResult, LiteralEncoder, LAMBDA},
    node::Variable,
    sat::{nlit, plit, pvar},
};

pub struct AssignmentEncoder {
    lhs: Rc<Variable>,
    rhs: SmtString,
    last_bound: Option<usize>,
    sign: bool,
}

impl AssignmentEncoder {
    pub fn new(lhs: Rc<Variable>, rhs: SmtString, sign: bool) -> Self {
        Self {
            lhs,
            rhs,
            sign,
            last_bound: None,
        }
    }

    fn encode_eq(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        let len_rhs = self.rhs.len();
        let bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;

        let mut result = EncodingResult::empty();
        if bound < len_rhs {
            // Trivially unsatisfiable
            let p = pvar();
            result.add_clause(vec![plit(p)]);
            result.add_assumption(nlit(p));
            return Ok(result);
        }

        let last_bound = self.last_bound.unwrap_or(0);
        if last_bound == bound {
            // Already encoded for this bound
            return Ok(result);
        }

        // Haven't encoded anything yet, was trivially unsatisfiable in previous call
        match last_bound.cmp(&len_rhs) {
            Ordering::Less => {
                for i in 0..len_rhs {
                    let chr = self.rhs[i];
                    let sub_var = dom_enc.string().get_sub(&self.lhs, i, chr).unwrap();
                    result.add_clause(vec![plit(sub_var)]);
                }
                if bound > len_rhs {
                    // Make sure the rest of lhs is empty
                    let lambda_sub = dom_enc
                        .string()
                        .get_sub(&self.lhs, len_rhs, LAMBDA)
                        .unwrap();
                    result.add_clause(vec![plit(lambda_sub)]);
                }
            }
            Ordering::Equal => {
                // Already encoded up to rhs length in previous iteration, make sure the rest of lhs is empty.
                let lambda_sub = dom_enc
                    .string()
                    .get_sub(&self.lhs, len_rhs, LAMBDA)
                    .unwrap();

                result.add_clause(vec![plit(lambda_sub)]);
            }
            Ordering::Greater => (), // Already encoded that remainder of lhs is empty
        }

        self.last_bound = Some(bound);

        Ok(result)
    }

    fn encode_ineq(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        let len_rhs = self.rhs.len();
        let bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;

        let mut result = EncodingResult::empty();

        if bound < len_rhs {
            // Trivially satisfiable

            return Ok(result);
        }

        let last_bound = self.last_bound.unwrap_or(0);
        // Haven't encoded anything yet, was trivially unsatisfiable in previous call

        if self.last_bound.is_none() || last_bound <= len_rhs {
            let mut clause = Vec::with_capacity(len_rhs);
            for i in 0..len_rhs {
                let chr = self.rhs[i];
                let sub_var = dom_enc.string().get_sub(&self.lhs, i, chr).unwrap();
                clause.push(nlit(sub_var));
            }

            match len_rhs.cmp(&bound) {
                Ordering::Less => {
                    // lhs might also be longer than rhs
                    let lambda_sub = dom_enc
                        .string()
                        .get_sub(&self.lhs, len_rhs, LAMBDA)
                        .unwrap();

                    clause.push(nlit(lambda_sub));
                    result.add_clause(clause);
                }
                Ordering::Equal => {
                    // Select the clause, in next iteration we will make sure the rest of lhs can also be non-empty
                    let selector = pvar();
                    clause.push(nlit(selector));
                    result.add_clause(clause);
                    result.add_assumption(plit(selector));
                }
                Ordering::Greater => (),
            }
        }

        self.last_bound = Some(bound);

        Ok(result)
    }
}

impl LiteralEncoder for AssignmentEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        bounds: &Domain,
        substitution: &DomainEncoding,
    ) -> Result<EncodingResult, EncodingError> {
        if self.sign {
            self.encode_eq(bounds, substitution)
        } else {
            self.encode_ineq(bounds, substitution)
        }
    }
}
