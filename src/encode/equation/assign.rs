//! Encoder for `assignment` type equations.
//! Assignments are of the form `x = w` where `x` is a variable and `w` is a constant word.

use std::{cmp::Ordering, rc::Rc};

use rustsat::types::Clause;

use smt_str::SmtString;

use crate::{
    context::Variable,
    domain::Domain,
    encode::{domain::DomainEncoding, EncodeLiteral, EncodingError, EncodingSink, LAMBDA},
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
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let len_rhs = self.rhs.len();
        let bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;

        if bound < len_rhs {
            // Trivially unsatisfiable
            let p = pvar();
            sink.add_unit(plit(p));
            sink.add_assumption(nlit(p));
            return Ok(());
        }

        let last_bound = self.last_bound.unwrap_or(0);
        if last_bound == bound {
            // Already encoded for this bound
            return Ok(());
        }

        // Haven't encoded anything yet, was trivially unsatisfiable in previous call
        match last_bound.cmp(&len_rhs) {
            Ordering::Less => {
                for i in 0..len_rhs {
                    let chr = self.rhs[i];
                    let sub_var = dom_enc.string().get_sub(&self.lhs, i, chr).unwrap();
                    sink.add_unit(plit(sub_var));
                }
                if bound > len_rhs {
                    // Make sure the rest of lhs is empty
                    let lambda_sub = dom_enc
                        .string()
                        .get_sub(&self.lhs, len_rhs, LAMBDA)
                        .unwrap();
                    sink.add_unit(plit(lambda_sub));
                }
            }
            Ordering::Equal => {
                // Already encoded up to rhs length in previous iteration, make sure the rest of lhs is empty.
                let lambda_sub = dom_enc
                    .string()
                    .get_sub(&self.lhs, len_rhs, LAMBDA)
                    .unwrap();

                sink.add_unit(plit(lambda_sub));
            }
            Ordering::Greater => (), // Already encoded that remainder of lhs is empty
        }

        self.last_bound = Some(bound);

        Ok(())
    }

    fn encode_ineq(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        let len_rhs = self.rhs.len();
        let bound = dom
            .get_string(&self.lhs)
            .and_then(|i| i.upper_finite())
            .unwrap() as usize;

        if bound < len_rhs {
            // Trivially satisfiable
            return Ok(());
        }

        let last_bound = self.last_bound.unwrap_or(0);
        // Haven't encoded anything yet, was trivially unsatisfiable in previous call

        if self.last_bound.is_none() || last_bound <= len_rhs {
            let mut clause = Clause::with_capacity(len_rhs);
            for i in 0..len_rhs {
                let chr = self.rhs[i];
                let sub_var = dom_enc.string().get_sub(&self.lhs, i, chr).unwrap();
                clause.add(nlit(sub_var));
            }

            match len_rhs.cmp(&bound) {
                Ordering::Less => {
                    // lhs might also be longer than rhs
                    let lambda_sub = dom_enc
                        .string()
                        .get_sub(&self.lhs, len_rhs, LAMBDA)
                        .unwrap();

                    clause.add(nlit(lambda_sub));
                    sink.add_clause(clause);
                }
                Ordering::Equal => {
                    // Select the clause, in next iteration we will make sure the rest of lhs can also be non-empty
                    let selector = pvar();
                    clause.add(nlit(selector));
                    sink.add_clause(clause);
                    sink.add_assumption(plit(selector));
                }
                Ordering::Greater => (),
            }
        }

        self.last_bound = Some(bound);

        Ok(())
    }
}

impl EncodeLiteral for AssignmentEncoder {
    fn _is_incremental(&self) -> bool {
        true
    }

    fn _reset(&mut self) {
        todo!()
    }

    fn encode(
        &mut self,
        dom: &Domain,
        dom_enc: &DomainEncoding,
        sink: &mut impl EncodingSink,
    ) -> Result<(), EncodingError> {
        if self.sign {
            self.encode_eq(dom, dom_enc, sink)
        } else {
            self.encode_ineq(dom, dom_enc, sink)
        }
    }
}
