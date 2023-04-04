use super::card::exactly_one;
use crate::{
    encode::LAMBDA,
    model::Variable,
    sat::{asLit, neg, pvar, Cnf, PVar},
};
use std::collections::{HashMap, HashSet};

use super::VariableBounds;

pub struct SubstitutionEncoding {
    encodings: HashMap<(Variable, usize, char), u32>,
}

impl SubstitutionEncoding {
    pub fn new() -> Self {
        Self {
            encodings: HashMap::new(),
        }
    }

    pub fn get(&self, var: &Variable, pos: usize, chr: char) -> Option<u32> {
        self.encodings.get(&(var.clone(), pos, chr)).cloned()
    }

    fn add(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        self.encodings.insert((var.clone(), pos, chr), v);
    }
}

pub struct SubstitutionEncoder<'a> {
    alphabet: &'a HashSet<char>,
    encoding: SubstitutionEncoding,
    last_bounds: Option<VariableBounds>,
}

impl<'a> SubstitutionEncoder<'a> {
    pub fn encode(&mut self, bounds: &VariableBounds) -> Cnf {
        let mut cnf = Cnf::new();
        for (var, bound) in bounds {
            let last_bound = self.pre_bounds(var).unwrap_or(0);

            for b in (last_bound..*bound).rev() {
                let mut pos_subs = vec![];
                for c in self.alphabet {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    self.encoding.add(var, b, *c, subvar);
                    pos_subs.push(subvar)
                }
                // Lambda
                let subvar_lambda = pvar();
                self.encoding.add(var, b, LAMBDA, subvar_lambda);
                pos_subs.push(subvar_lambda);

                // If current position is LAMBDA, then all following must be LAMBDA
                if b + 1 < *bound {
                    let clause = vec![
                        neg(subvar_lambda),
                        asLit(self.encoding.get(var, b + 1, LAMBDA).unwrap()),
                    ];
                    cnf.push(clause);
                }

                // Exactly one needs to be selected
                cnf.extend(exactly_one(&pos_subs));
            }
        }

        self.last_bounds = Some(bounds.clone());
        cnf
    }

    fn pre_bounds(&self, var: &Variable) -> Option<usize> {
        match &self.last_bounds {
            Some(bs) => bs.get(var).cloned(),
            None => None,
        }
    }

    pub fn get_encoding(&self) -> &SubstitutionEncoding {
        &self.encoding
    }
}

mod tests {
    use super::*;

    #[test]
    fn all_subst_defined() {
        todo!()
    }

    #[test]
    fn all_subst_defined_incremental() {
        todo!()
    }
}
