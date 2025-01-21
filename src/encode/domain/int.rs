use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::DomainEncoding;

use crate::sat::{plit, PVar};
use crate::{
    bounds::{Domain, Interval},
    encode::{card::IncrementalEO, EncodingResult},
    node::{canonical::Assignment, Sort, Sorted, Variable},
    sat::pvar,
};

#[derive(Clone, Debug, Default)]
pub struct IntDomain {
    encodings: IndexMap<(Rc<Variable>, i64), PVar>,
}

impl IntDomain {
    /// Sets the Boolean variable that is true if the variable has the given length.
    /// Panics if the variable was already set.
    pub fn insert(&mut self, var: Rc<Variable>, value: i64, pvar: PVar) {
        assert!(
            var.sort() == Sort::Int,
            "Variable {} is not an integer",
            var
        );
        let ok = self.encodings.insert((var, value), pvar);
        assert!(ok.is_none());
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<Variable>, i64, &PVar)> {
        self.encodings
            .iter()
            .map(|((var, value), v)| (var, *value, v))
    }

    pub fn get(&self, var: &Rc<Variable>, value: i64) -> Option<PVar> {
        assert!(
            var.sort() == Sort::Int,
            "Variable {} is not an integer",
            var
        );

        self.encodings.get(&(var.clone(), value)).cloned()
    }

    pub(crate) fn get_model(&self, solver: &cadical::Solver) -> Assignment {
        if solver.status() != Some(true) {
            panic!("Solver is not in a SAT state")
        }
        let mut model = Assignment::default();
        for (var, l, v) in self.iter() {
            if let Some(true) = solver.value(plit(*v)) {
                let ok = model.assign(var.clone(), l);
                assert!(ok.is_none());
            }
        }
        model
    }
}

pub struct IntegerEncoder {
    last_domains: Option<Domain>,
    /// Maps each variable to an Incremental exact-one encoder that is used to encode the variable's domain.
    var_len_eo_encoders: IndexMap<Variable, IncrementalEO>,
}

impl IntegerEncoder {
    pub fn new() -> Self {
        Self {
            last_domains: None,
            var_len_eo_encoders: IndexMap::new(),
        }
    }

    pub fn encode(&mut self, bounds: &Domain, encoding: &mut DomainEncoding) -> EncodingResult {
        let res = self.encode_int_vars(bounds, encoding);

        self.last_domains = Some(bounds.clone());
        res
    }

    fn get_last_dom(&self, var: &Variable) -> Option<Interval> {
        self.last_domains.as_ref().and_then(|doms| doms.get(var))
    }

    fn encode_int_vars(
        &mut self,
        bounds: &Domain,
        encoding: &mut DomainEncoding,
    ) -> EncodingResult {
        let mut res = EncodingResult::empty();

        for (int_var, bound) in bounds.iter().filter(|(v, b)| v.sort().is_int()) {
            let mut len_choices = vec![];
            let last_upper_bound = self
                .get_last_dom(int_var)
                .map(|b| (b.upper_finite().unwrap()));
            // from last_upper_bound to upper bound
            let last_lower_bound = self
                .get_last_dom(int_var)
                .map(|b| b.lower_finite().unwrap());

            let lower = bound.lower_finite().unwrap_or(0);
            let upper = bound.upper_finite().unwrap();
            for len in lower..=upper {
                if last_lower_bound.map(|ll| len < ll).unwrap_or(true)
                    || last_upper_bound.map(|lu| len > lu).unwrap_or(true)
                {
                    // This lenght is not in the previous domain, so we need to encode it
                    let choice = pvar();
                    len_choices.push(choice);
                    encoding.int.insert(int_var.clone(), len as i64, choice);
                }
            }
            // Exactly one length must be true
            let eo = self
                .var_len_eo_encoders
                .entry(int_var.as_ref().clone())
                .or_default()
                .add(&len_choices);

            res.extend(eo);
        }
        res
    }
}
