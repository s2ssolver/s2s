use indexmap::{IndexMap, IndexSet};

use crate::{
    encode::{
        AlignmentEncoder, ConstraintEncoder, MddEncoder, NFAEncoder, RegularConstraintEncoder,
        WordEquationEncoder,
    },
    error::Error,
    instance::Instance,
    model::{
        formula::{Alphabet, Literal},
        Constraint,
    },
    sat::{as_lit, pvar, PLit},
};

/// A definitional literal is a literal that is defines a constraint.
type Definitional = PLit;

type Watcher = PLit;

/// A watcher is a literal is a literal that is injected into all clauses of a constraint encoding.
/// It used to check whether an encoding is part of an UNSAT core using the `failed` interface.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EncodingContext {
    constraint: Constraint,
    definitional: Definitional,
    watcher: Watcher,
}
impl EncodingContext {
    fn new(constraint: Constraint, definitional: Definitional, watcher: Watcher) -> Self {
        Self {
            constraint,
            definitional,
            watcher,
        }
    }

    /// Returns the defining literal of the constraint.
    pub fn definitional(&self) -> Definitional {
        self.definitional
    }

    /// Returns the watcher literal for the constraint.
    pub fn watcher(&self) -> Watcher {
        self.watcher
    }

    /// Returns the constraint.
    pub fn constraint(&self) -> &Constraint {
        &self.constraint
    }
}

pub(super) struct EncodingManager {
    /// The set of all constraints that are currently encoded, along with their defining literal and watcher.
    contexts: IndexSet<EncodingContext>,
    /// Mapping from constraint to its context.
    ctx_by_constraint: IndexMap<Constraint, EncodingContext>,
    /// Mapping from watcher literal to its context.
    ctx_by_watcher: IndexMap<Watcher, EncodingContext>,

    ctx_by_literal: IndexMap<Literal, EncodingContext>,

    /// Mapping from context to its encoder.
    encoders: IndexMap<EncodingContext, Box<dyn ConstraintEncoder>>,
}

impl EncodingManager {
    pub fn new() -> Self {
        Self {
            contexts: IndexSet::new(),
            ctx_by_constraint: IndexMap::new(),
            ctx_by_watcher: IndexMap::new(),
            ctx_by_literal: IndexMap::new(),
            encoders: IndexMap::new(),
        }
    }

    fn add_context(&mut self, ctx: EncodingContext, lit: &Literal) {
        self.contexts.insert(ctx.clone());
        self.ctx_by_constraint
            .insert(ctx.constraint.clone(), ctx.clone());
        self.ctx_by_watcher.insert(ctx.watcher, ctx.clone());
        self.ctx_by_literal.insert(lit.clone(), ctx);
    }

    pub fn add(&mut self, lit: &Literal, def: PLit, instance: &Instance) -> Result<(), Error> {
        let mut con = Constraint::try_from(lit.clone())?;

        // Pre-compile NFAs for regular constraints.
        if let Constraint::RegularConstraint(rc) = &mut con {
            let alphabet = instance.alphabet();
            rc.compile(Some(&alphabet))?;
        }

        let watcher = as_lit(pvar());

        let ctx = EncodingContext::new(con.clone(), def, watcher);
        self.add_context(ctx.clone(), lit);

        let encoder = Self::encoder_for_constraint(&con)?;
        self.encoders.insert(ctx, encoder);
        Ok(())
    }

    pub fn num_constraints(&self) -> usize {
        self.contexts.len()
    }

    /// Instatiates a new encoder for the given constraint.
    fn encoder_for_constraint(con: &Constraint) -> Result<Box<dyn ConstraintEncoder>, Error> {
        match con {
            Constraint::WordEquation(eq) => Ok(Box::new(AlignmentEncoder::new(eq.clone()))),
            Constraint::LinearConstraint(lc) => Ok(Box::new(MddEncoder::new(lc.clone()))),
            Constraint::RegularConstraint(rc) => Ok(Box::new(NFAEncoder::new(rc.clone())?)),
            Constraint::BoolVarConstraint(v, pol) => {
                Ok(Box::new(BoolVarEncoder::new(v.clone(), *pol)))
            }
        }
    }

    pub fn for_literal(&self, lit: &Literal) -> Option<&EncodingContext> {
        self.ctx_by_literal.get(lit)
    }

    pub fn iter(
        &mut self,
    ) -> impl Iterator<Item = (&EncodingContext, &mut Box<dyn ConstraintEncoder>)> {
        self.encoders.iter_mut()
    }
}
