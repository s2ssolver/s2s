use crate::{
    instance::Instance,
    model::{
        formula::{Atom, Literal, NNFFormula},
        Sort, Variable,
    },
    sat::{as_lit, neg, pvar, PLit},
};
use std::collections::HashMap;

pub struct Definitions {
    literal2def: HashMap<Literal, PLit>,
    def2literal: HashMap<PLit, Literal>,
}

impl Definitions {
    fn new() -> Self {
        Self {
            literal2def: HashMap::new(),
            def2literal: HashMap::new(),
        }
    }

    fn insert(&mut self, literal: Literal, var: PLit) {
        self.literal2def.insert(literal.clone(), var);
        self.def2literal.insert(var, literal);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&PLit, &Literal)> {
        self.def2literal.iter()
    }

    /// Defines a literal and returns the corresponding definitional variable/literal.
    /// If the literal is already defined, the already created variable is returned.
    /// If the negation of the literal is already defined, the negation of the already created variable/literal is returned.
    fn define(&mut self, literal: &Literal) -> PLit {
        let negated = literal.negated();
        let var = if let Some(var) = self.literal2def.get(&literal) {
            *var
        } else if let Some(var) = self.literal2def.get(&negated) {
            let var = -*var;
            self.insert(literal.clone(), var);
            var
        } else {
            let var = if literal.is_neg() {
                neg(pvar())
            } else {
                as_lit(pvar())
            };
            self.insert(literal.clone(), var);
            var
        };

        assert!((literal.is_neg()) == (var < 0));
        assert!((literal.is_pos()) == (var > 0));
        var
    }
}

pub struct Abstraction {
    definitions: Definitions,
    skeleton: NNFFormula,
}

impl Abstraction {
    pub fn new(instance: &mut Instance) -> Self {
        let mut defs = Definitions::new();

        let skeleton = Self::build(&mut defs, &instance.get_formula().clone().into(), instance);

        Self {
            definitions: defs,
            skeleton,
        }
    }

    /// Builds the Boolean skeleton of the formula and stores the definitions in `defs`.
    /// Returns the root literal of the skeleton.
    fn build(defs: &mut Definitions, root: &NNFFormula, instance: &mut Instance) -> NNFFormula {
        match root {
            NNFFormula::Literal(l) => {
                let defv = defs.define(l);
                let var = instance
                    .vars_of_sort(Sort::Bool)
                    .find(|v| match v {
                        Variable::Bool { value, .. } => *value == defv.abs() as u32,
                        _ => unreachable!(),
                    })
                    .cloned();
                let var = match var {
                    None => {
                        let v = Variable::Bool {
                            name: format!("def_{}", defv),
                            value: defv.abs() as u32,
                        };
                        instance.add_var(v.clone());
                        v
                    }
                    Some(v) => v,
                };
                let atom: Atom = Atom::BoolVar(var);
                if l.is_pos() {
                    NNFFormula::Literal(Literal::Pos(atom))
                } else {
                    NNFFormula::Literal(Literal::Neg(atom))
                }
            }
            NNFFormula::Or(fs) => {
                let mut children = vec![];
                for child in fs {
                    children.push(Self::build(defs, child, instance));
                }
                NNFFormula::or(children)
            }
            NNFFormula::And(fs) => {
                let mut children = vec![];
                for child in fs {
                    children.push(Self::build(defs, child, instance));
                }
                NNFFormula::and(children)
            }
        }
    }

    /// Returns the skeleton of the formula.
    pub fn get_skeleton(&self) -> &NNFFormula {
        &self.skeleton
    }

    /// Returns the definitions of the abstraction.
    pub fn definitions(&self) -> &Definitions {
        &self.definitions
    }
}

#[cfg(test)]
mod test {

    use quickcheck_macros::quickcheck;

    use crate::model::formula::Predicate;

    use super::*;

    #[quickcheck]
    fn define_new(p: Predicate) {
        let mut defs = Definitions::new();

        let literal = Literal::Pos(Atom::Predicate(p));

        let var = defs.define(&literal);
        assert!(var > 0);
    }

    #[quickcheck]
    fn define_negated(p: Predicate) {
        let mut defs = Definitions::new();

        let literal = Literal::Pos(Atom::Predicate(p.clone()));
        let neg_literal = Literal::Neg(Atom::Predicate(p));

        let var = defs.define(&literal);
        assert!(var > 0);
        let neg_var = defs.define(&neg_literal);
        assert!(neg_var == -var);
    }
    #[quickcheck]
    fn define_negated_rev(p: Predicate) {
        let mut defs = Definitions::new();

        let literal = Literal::Pos(Atom::Predicate(p.clone()));
        let neg_literal = Literal::Neg(Atom::Predicate(p));

        let neg_var = defs.define(&neg_literal);
        assert!(neg_var < 0);
        let var = defs.define(&literal);
        assert!(neg_var == -var);
    }
}
