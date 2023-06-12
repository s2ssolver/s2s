use indexmap::IndexMap;

use crate::{
    formula::{Atom, Formula, Predicate},
    model::{
        linears::{LinearArithFactor, LinearArithTerm, LinearConstraint},
        words::{Pattern, Symbol, WordEquation},
        VarManager, Variable,
    },
    PreprocessingResult,
};

#[derive(Debug, Clone, Default)]
pub struct Substitutions {
    subs: IndexMap<Variable, Pattern>,
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
            Some(p) => {
                if p.len() < pat.len() {
                    pat.clone()
                } else {
                    p.clone()
                }
            }

            None => pat.clone(),
        };
        self.subs.insert(var.clone(), rhs.clone());
    }

    pub fn extend(&mut self, other: &Substitutions) {
        for (v, p) in other.iter() {
            self.add(v, p);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Variable, &Pattern)> {
        self.subs.iter()
    }
}

fn apply_substitutions_predicate(
    pred: &Predicate,
    substitutions: &Substitutions,
    var_manager: &VarManager,
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
        Predicate::LinearConstraint(lincon) => {
            let mut lhs = LinearArithTerm::new();
            for fac in lincon.lhs().iter() {
                match fac {
                    LinearArithFactor::VarCoeff(v, c) => {
                        let str_var = var_manager.length_str_var(v).unwrap();
                        match substitutions.subs.get(str_var) {
                            Some(sub) => {
                                if sub.is_constant() {
                                    lhs.add_factor(LinearArithFactor::Const(
                                        c * sub.len() as isize,
                                    ));
                                } else {
                                    // Contains the variable, add another factor
                                    lhs.add_factor(LinearArithFactor::VarCoeff(v.clone(), *c));
                                    debug_assert!(
                                        sub.count(&Symbol::Variable(str_var.clone())) == 1
                                    );
                                    lhs.add_factor(LinearArithFactor::Const(
                                        *c * (sub.len() as isize - 1),
                                    ));
                                }
                            }
                            None => lhs.add_factor(LinearArithFactor::VarCoeff(v.clone(), *c)),
                        }
                    }
                    LinearArithFactor::Const(c) => lhs.add_factor(LinearArithFactor::Const(*c)),
                }
            }
            let mut new_rhs = LinearArithTerm::new();
            new_rhs.add_factor(LinearArithFactor::Const(lincon.rhs()));
            let new_lincon =
                LinearConstraint::from_linear_arith_term(&lhs, &new_rhs, lincon.typ.clone());
            log::info!(
                "Applied substitutions {} to {}: {}",
                substitutions,
                lincon,
                new_lincon
            );
            PreprocessingResult::Changed(Predicate::LinearConstraint(new_lincon))
        }
    }
}

pub fn apply_substitutions(
    formula: &Formula,
    substitutions: &Substitutions,
    var_manager: &VarManager,
) -> PreprocessingResult<Formula> {
    match formula {
        Formula::Atom(a) => match a {
            Atom::Predicate(p) => {
                match apply_substitutions_predicate(p, substitutions, var_manager) {
                    PreprocessingResult::Unchanged => PreprocessingResult::Unchanged,
                    PreprocessingResult::Changed(c) => {
                        PreprocessingResult::Changed(Formula::predicate(c))
                    }
                    PreprocessingResult::False => PreprocessingResult::False,
                    PreprocessingResult::True => PreprocessingResult::True,
                }
            }
            _ => PreprocessingResult::Unchanged,
        },
        Formula::Or(fs) => {
            let mut changed = false;
            let mut new_fs = Vec::new();
            for f in fs {
                match apply_substitutions(f, substitutions, var_manager) {
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
                match apply_substitutions(f, substitutions, var_manager) {
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
        Formula::Not(f) => match apply_substitutions(f, substitutions, var_manager) {
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
