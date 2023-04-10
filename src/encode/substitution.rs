use super::{card::exactly_one, EncodingResult};
use crate::{
    encode::LAMBDA,
    model::Variable,
    sat::{as_lit, neg, pvar, Cnf, PLit, PVar},
};
use std::collections::{HashMap, HashSet};

use super::VariableBounds;

pub struct SubstitutionEncoding {
    encodings: HashMap<(Variable, usize, char), PVar>,
    alphabet: HashSet<char>,
}

impl SubstitutionEncoding {
    pub fn new(alphabet: HashSet<char>) -> Self {
        Self {
            encodings: HashMap::new(),
            alphabet,
        }
    }

    pub fn get(&self, var: &Variable, pos: usize, chr: char) -> Option<PVar> {
        self.encodings.get(&(var.clone(), pos, chr)).cloned()
    }

    pub fn get_lit(&self, var: &Variable, pos: usize, chr: char) -> Option<PLit> {
        self.get(var, pos, chr).map(as_lit)
    }

    fn add(&mut self, var: &Variable, pos: usize, chr: char, v: PVar) {
        self.encodings.insert((var.clone(), pos, chr), v);
    }

    pub fn alphabet(&self) -> &HashSet<char> {
        &self.alphabet
    }

    pub fn alphabet_lambda(&self) -> HashSet<char> {
        let l = HashSet::from_iter(vec![LAMBDA]);
        self.alphabet.union(&l).cloned().collect()
    }
}

pub struct SubstitutionEncoder {
    encoding: SubstitutionEncoding,
    vars: HashSet<Variable>,
    last_bounds: Option<VariableBounds>,
}

impl SubstitutionEncoder {
    pub fn new(alphabet: HashSet<char>, vars: HashSet<Variable>) -> Self {
        Self {
            encoding: SubstitutionEncoding::new(alphabet.clone()),
            vars,
            last_bounds: None,
        }
    }

    pub fn encode(&mut self, bounds: &VariableBounds) -> EncodingResult {
        let mut cnf = Cnf::new();
        log::debug!("Encoding substitutions");
        for var in &self.vars {
            let bound = bounds.get(var);
            let last_bound = self.pre_bounds(var).unwrap_or(0);
            log::debug!("Variable {} - Positions {} to {}", var, last_bound, bound);
            // Todo: this is bad because it clones the alphabet
            let alph = self.encoding.alphabet.clone();
            for b in (last_bound..bound).rev() {
                let mut pos_subs = vec![];
                for c in &alph {
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
                if b + 1 < bound {
                    let clause = vec![
                        neg(subvar_lambda),
                        as_lit(self.encoding.get(var, b + 1, LAMBDA).unwrap()),
                    ];
                    cnf.push(clause);
                }
                // Exactly one needs to be selected
                cnf.extend(exactly_one(&pos_subs));
            }
        }

        self.last_bounds = Some(bounds.clone());
        EncodingResult::Cnf(cnf)
    }

    fn pre_bounds(&self, var: &Variable) -> Option<usize> {
        match &self.last_bounds {
            Some(bs) => Some(bs.get(var)),
            None => None,
        }
    }

    pub fn get_encoding(&self) -> &SubstitutionEncoding {
        &self.encoding
    }

    pub fn get_substitutions(&self, solver: &cadical::Solver) -> HashMap<&Variable, String> {
        let mut subs = HashMap::new();
        for v in &self.vars {
            let mut sub = String::new();
            for b in 0..self.pre_bounds(v).unwrap_or(0) {
                for c in self.encoding.alphabet_lambda() {
                    let lit = self.encoding.get_lit(&v, b, c).unwrap();
                    if let Some(true) = solver.value(lit) {
                        if c == LAMBDA {
                            sub.push('_');
                        } else {
                            sub.push(c);
                        }
                    }
                }
            }
            subs.insert(v, sub);
        }
        subs
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
