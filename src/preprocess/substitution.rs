use indexmap::IndexMap;

use crate::{
    formula::{Atom, Formula, Predicate},
    model::{
        words::{Pattern, Symbol, WordEquation},
        Variable,
    },
    PreprocessingResult,
};

#[derive(Debug, Clone, Default)]
pub struct Substitutions {
    subs: IndexMap<Variable, Option<Pattern>>,
}

impl Substitutions {
    pub fn new() -> Self {
        Self {
            subs: IndexMap::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.subs.is_empty()
    }

    pub fn add(&mut self, var: &Variable, pat: &Pattern) {
        let rhs = match self.subs.get(var) {
            Some(Some(p)) => {
                if p.len() < pat.len() {
                    Some(pat.clone())
                } else {
                    Some(p.clone())
                }
            }
            Some(None) => None,
            None => Some(pat.clone()),
        };
        self.subs.insert(var.clone(), rhs.clone());
    }

    pub fn extend(&mut self, other: &Substitutions) {
        for (v, p) in other.iter() {
            self.add(v, p);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Pattern)> {
        self.subs
            .iter()
            .filter_map(|(v, p)| p.as_ref().map(|p| (v, p)))
    }

    pub fn conflicting(&self) -> bool {
        self.subs.iter().any(|(_, p)| p.is_none())
    }
}

fn apply_substitutions_predicate(
    pred: &Predicate,
    substitutions: &Substitutions,
) -> PreprocessingResult<Predicate> {
    match pred {
        Predicate::WordEquation(eq) => {
            let mut lhs_new = eq.lhs().clone();
            let mut rhs_new = eq.rhs().clone();
            for (v, re) in substitutions.iter() {
                lhs_new = lhs_new.replace(&Symbol::Variable(v.clone()), re);
                rhs_new = rhs_new.replace(&Symbol::Variable(v.clone()), re);
            }
            let eq_new = WordEquation::new(lhs_new, rhs_new);
            if &eq_new == eq {
                PreprocessingResult::Unchanged
            } else {
                log::trace!(
                    "Applied substitutions {} to {}: {}",
                    substitutions,
                    eq,
                    eq_new
                );
                PreprocessingResult::Changed(Predicate::WordEquation(eq_new))
            }
        }
        Predicate::RegularConstraint(_, _) => todo!(),
        Predicate::LinearConstraint(_) => PreprocessingResult::Unchanged,
    }
}

pub fn apply_substitutions(
    formula: &Formula,
    substitutions: &Substitutions,
) -> PreprocessingResult<Formula> {
    match formula {
        Formula::Atom(a) => match a {
            Atom::Predicate(p) => match apply_substitutions_predicate(p, substitutions) {
                PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
                PreprocessingResult::Changed(c) => {
                    PreprocessingResult::Changed(Formula::predicate(c))
                }
                PreprocessingResult::False => PreprocessingResult::False,
                PreprocessingResult::True => PreprocessingResult::True,
            },
            _ => PreprocessingResult::Unchanged,
        },
        Formula::Or(fs) => {
            let mut changed = false;
            let mut new_fs = Vec::new();
            for f in fs {
                match apply_substitutions(f, substitutions) {
                    PreprocessingResult::Unchanged => new_fs.push(f.clone()),
                    PreprocessingResult::Changed(c) => {
                        changed = true;
                        new_fs.push(c);
                    }
                    PreprocessingResult::False => (),
                    PreprocessingResult::True => return PreprocessingResult::True,
                }
            }
            if changed {
                PreprocessingResult::Changed(Formula::or(new_fs))
            } else {
                PreprocessingResult::Unchanged
            }
        }
        Formula::And(fs) => {
            let mut changed = false;
            let mut new_fs = Vec::new();
            for f in fs {
                match apply_substitutions(f, substitutions) {
                    PreprocessingResult::Unchanged => new_fs.push(f.clone()),
                    PreprocessingResult::Changed(c) => {
                        changed = true;
                        new_fs.push(c);
                    }
                    PreprocessingResult::True => (),
                    PreprocessingResult::False => return PreprocessingResult::False,
                }
            }
            if changed {
                PreprocessingResult::Changed(Formula::and(new_fs))
            } else {
                PreprocessingResult::Unchanged
            }
        }
        Formula::Not(f) => match apply_substitutions(f, substitutions) {
            PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
            PreprocessingResult::Changed(c) => PreprocessingResult::Changed(Formula::not(c)),
            PreprocessingResult::False => PreprocessingResult::True,
            PreprocessingResult::True => PreprocessingResult::False,
        },
    }
}

pub fn infer_subsitutions(pred: &Predicate) -> Substitutions {
    match pred {
        Predicate::WordEquation(weq) => {
            let mut subs = Substitutions::new();

            if let Some(Symbol::Variable(v)) = weq.lhs().first() {
                let rest = weq
                    .lhs()
                    .factor(1, weq.lhs().len())
                    .unwrap_or(Pattern::empty());
                let mut i = 0;
                while i < weq.rhs().len() {
                    match &weq.rhs()[i] {
                        Symbol::Constant(c) => match rest.first() {
                            Some(Symbol::Constant(snd)) => {
                                if c != snd {
                                    i += 1;
                                } else {
                                    break;
                                }
                            }
                            None => i += 1,
                            _ => break,
                        },
                        Symbol::Variable(_) => break,
                    }
                }
                if i > 0 {
                    let mut s = weq.rhs().factor(0, i).unwrap();
                    if i < weq.rhs().len() {
                        s.append(&Symbol::Variable(v.clone()));
                    }
                    subs.add(v, &s);
                }
            } else if let Some(Symbol::Variable(v)) = weq.rhs().first() {
                let rest = weq
                    .lhs()
                    .factor(1, weq.lhs().len())
                    .unwrap_or(Pattern::empty());
                let mut i = 0;
                while i < weq.lhs().len() {
                    match &weq.lhs()[i] {
                        Symbol::Constant(c) => match rest.first() {
                            Some(Symbol::Constant(snd)) => {
                                if c != snd {
                                    i += 1;
                                } else {
                                    break;
                                }
                            }
                            None => i += 1,
                            _ => break,
                        },
                        Symbol::Variable(_) => break,
                    }
                }
                if i > 0 {
                    let mut s = weq.lhs().factor(0, i).unwrap();
                    if i < weq.lhs().len() {
                        s.append(&Symbol::Variable(v.clone()));
                    }
                    subs.add(v, &s);
                }
            }
            if !subs.is_empty() {
                log::debug!("Inferred substitutions from {}: {}", weq, subs);
            }

            subs
        }
        Predicate::RegularConstraint(_, _) => todo!("Not supported yet"),
        Predicate::LinearConstraint(_) => Substitutions::new(),
    }
}
