use super::{card::exactly_one, EncodingResult};
use crate::{
    encode::LAMBDA,
    model::Variable,
    sat::{as_lit, neg, pvar, Cnf, PLit, PVar},
};
use std::collections::{HashMap, HashSet};

use super::VariableBounds;

#[derive(Clone, Debug)]
pub struct SubstitutionEncoding {
    encodings: HashMap<(Variable, usize, char), PVar>,
    bounds: VariableBounds,
    alphabet: HashSet<char>,
}

impl SubstitutionEncoding {
    pub fn new(alphabet: HashSet<char>, bounds: VariableBounds) -> Self {
        Self {
            encodings: HashMap::new(),
            alphabet,
            bounds,
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

    #[allow(dead_code)]
    pub fn alphabet(&self) -> &HashSet<char> {
        &self.alphabet
    }

    pub fn alphabet_lambda(&self) -> HashSet<char> {
        let l = HashSet::from_iter(vec![LAMBDA]);
        self.alphabet.union(&l).cloned().collect()
    }

    fn vars(&self) -> HashSet<&Variable> {
        self.encodings.keys().map(|(v, _, _)| v).collect()
    }

    /// Reads the substitutions from the model.
    /// Panics if the solver is not in a SAT state.
    #[allow(dead_code)]
    pub fn get_substitutions(&self, solver: &cadical::Solver) -> HashMap<Variable, String> {
        if solver.status() != Some(true) {
            panic!("Solver is not in a SAT state")
        }
        let mut subs = HashMap::new();
        for var in self.vars() {
            // initialize substitutions
            subs.insert(var.clone(), vec![None; self.bounds.get(var)]);
        }
        for ((var, pos, chr), _v) in self.encodings.iter() {
            if let Some(true) = solver.value(as_lit(self.get(var, *pos, *chr).unwrap())) {
                let sub = subs.get_mut(var).unwrap();
                // This could be more efficient by going over the positions only once, however, this way we can check for invalid substitutions
                assert!(
                    sub[*pos].is_none(),
                    "Multiple substitutions for {} at position {}",
                    var,
                    pos
                );

                sub[*pos] = Some(*chr);
            }
        }
        let mut subs_str = HashMap::new();
        for (var, sub) in subs.into_iter() {
            let mut s = String::new();
            for c in sub.iter() {
                match c {
                    Some(LAMBDA) => {}
                    Some(c) => s.push(*c),
                    None => panic!("No substitution for {} at position {}", var, s.len()),
                }
            }
            subs_str.insert(var.clone(), s);
        }
        subs_str
    }
}

pub struct SubstitutionEncoder {
    encoding: Option<SubstitutionEncoding>,
    vars: HashSet<Variable>,
    last_bounds: Option<VariableBounds>,
    alphabet: HashSet<char>,
}

impl SubstitutionEncoder {
    pub fn new(alphabet: HashSet<char>, vars: HashSet<Variable>) -> Self {
        Self {
            encoding: None,
            vars,
            alphabet,
            last_bounds: None,
        }
    }

    pub fn encode(&mut self, bounds: &VariableBounds) -> EncodingResult {
        let mut cnf = Cnf::new();
        if self.encoding.is_none() {
            self.encoding = Some(SubstitutionEncoding::new(
                self.alphabet.clone(),
                bounds.clone(),
            ));
        }
        log::debug!("Encoding substitutions");
        for var in &self.vars {
            let bound = bounds.get(var);
            let last_bound = self.pre_bounds(var).unwrap_or(0);
            let encoding = self.encoding.as_mut().unwrap();

            // Todo: this is bad because it clones the alphabet
            let alph = self.alphabet.clone();
            for b in (last_bound..bound).rev() {
                let mut pos_subs = vec![];
                for c in &alph {
                    // subvar <--> `var` at position `b` is substituted with `c`
                    let subvar = pvar();
                    encoding.add(var, b, *c, subvar);
                    pos_subs.push(subvar)
                }
                // Lambda
                let subvar_lambda = pvar();
                encoding.add(var, b, LAMBDA, subvar_lambda);
                pos_subs.push(subvar_lambda);

                // If current position is LAMBDA, then all following must be LAMBDA
                if b + 1 < bound {
                    let clause = vec![
                        neg(subvar_lambda),
                        as_lit(encoding.get(var, b + 1, LAMBDA).unwrap()),
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
        self.last_bounds.as_ref().map(|bs| bs.get(var))
    }

    /// Returns the encoding for the substitutions.
    /// Returns `None` if the encoding has not been created yet, i.e., if `encode` has not been called.
    pub fn get_encoding(&self) -> Option<&SubstitutionEncoding> {
        self.encoding.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{encode::VariableBounds, model::Variable};

    use super::SubstitutionEncoder;

    #[test]
    fn all_subst_defined() {
        let var = Variable::tmp_var(crate::model::Sort::String);
        let alphabet = HashSet::from_iter(vec!['a', 'b', 'c']);
        let vars = HashSet::from_iter(vec![var.clone()]);
        let mut encoder = SubstitutionEncoder::new(alphabet, vars);
        let mb = 10;
        let bounds = VariableBounds::new(mb);

        encoder.encode(&bounds);

        for b in 0..mb {
            for c in encoder.get_encoding().unwrap().alphabet_lambda() {
                assert!(encoder
                    .get_encoding()
                    .unwrap()
                    .get_lit(&var, b, c)
                    .is_some());
            }
        }
    }
}
