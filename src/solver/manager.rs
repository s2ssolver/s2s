use std::{collections::HashSet, time::Instant};

use indexmap::{IndexMap, IndexSet};

use crate::{
    bounds::Bounds,
    encode::{
        domain::{get_int_substitutions, get_str_substitutions, DomainEncoder, DomainEncoding},
        get_encoder, ConstraintEncoder, EncodingResult,
    },
    error::Error,
    instance::Instance,
    model::{
        formula::{Alphabet, Literal},
        Constraint, Substitution,
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
    is_asserted: bool,
}
impl EncodingContext {
    fn new(
        constraint: Constraint,
        definitional: Definitional,
        watcher: Watcher,
        is_asserted: bool,
    ) -> Self {
        Self {
            constraint,
            definitional,
            watcher,
            is_asserted,
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

    /// Returns true if the constraint is asserted.
    pub fn is_asserted(&self) -> bool {
        self.is_asserted
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

    watchers: IndexMap<EncodingContext, Vec<PLit>>,

    domain_encoder: DomainEncoder,
}

impl EncodingManager {
    pub fn new(instance: &Instance) -> Self {
        let dom_encoder = DomainEncoder::new(Self::calc_alphabet(instance));

        Self {
            contexts: IndexSet::new(),
            ctx_by_constraint: IndexMap::new(),
            ctx_by_watcher: IndexMap::new(),
            ctx_by_literal: IndexMap::new(),
            encoders: IndexMap::new(),
            watchers: IndexMap::new(),
            domain_encoder: dom_encoder,
        }
    }

    fn calc_alphabet(instance: &Instance) -> IndexSet<char> {
        let mut alphabet = instance.get_formula().alphabet();
        // Make sure the alphabet contains at least one character

        let mut next_chr: u32 = 'a' as u32;

        for _ in 0..instance.get_formula().vars().len() {
            while alphabet.contains(&char::from_u32(next_chr).unwrap()) {
                next_chr += 1;
            }
            let chr = char::from_u32(next_chr).unwrap();
            alphabet.insert(chr);
        }
        log::debug!("Alphabet: {:?}", alphabet);
        alphabet
    }

    fn add_context(&mut self, ctx: EncodingContext, lit: &Literal) {
        self.contexts.insert(ctx.clone());
        self.ctx_by_constraint
            .insert(ctx.constraint.clone(), ctx.clone());
        self.ctx_by_watcher.insert(ctx.watcher, ctx.clone());
        self.ctx_by_literal.insert(lit.clone(), ctx);
    }

    pub fn add(
        &mut self,
        lit: &Literal,
        def: PLit,
        instance: &mut Instance,
        is_asserted: bool,
    ) -> Result<(), Error> {
        let mut con = Constraint::try_from(lit.clone())?;

        // Pre-compile NFAs for regular constraints.
        if let Constraint::RegularConstraint(rc) = &mut con {
            let alphabet = instance.alphabet();
            rc.compile(Some(&alphabet))?;
        }

        let watcher = as_lit(pvar());

        let ctx = EncodingContext::new(con.clone(), def, watcher, is_asserted);
        self.add_context(ctx.clone(), lit);

        let encoder = get_encoder(&con);
        self.encoders.insert(ctx, encoder);
        Ok(())
    }

    pub fn register_assumptions(&mut self, ctx: &EncodingContext, lit: &PLit) {
        self.watchers.entry(ctx.clone()).or_default().push(*lit);
    }
    pub fn clear_assumptions(&mut self) {
        self.watchers = IndexMap::new();
    }

    pub fn get_watching_literals(&self, ctx: &EncodingContext) -> Vec<PLit> {
        let mut watchers = self.watchers.get(ctx).cloned().unwrap_or(Vec::new());
        watchers.push(ctx.watcher());
        watchers
    }

    /// Encodes the problem instance with the given bounds.
    /// Returns the encoding result.
    pub fn encode_bounded(
        &mut self,
        bounds: &Bounds,
        instance: &Instance,
    ) -> Result<EncodingResult, Error> {
        let mut encoding = EncodingResult::empty();
        if self.num_constraints() == 0 {
            return Ok(EncodingResult::Trivial(true));
        }

        // Check if the only constraint is a single (positive) word equation adn call sharpen_bounds

        // Encode the domain
        let ts = Instant::now();
        let domain_clauses = self.domain_encoder.encode(bounds, instance);
        log::debug!(
            "Encoded domain for all variables with {} clauses ({} ms)",
            domain_clauses.clauses(),
            ts.elapsed().as_millis()
        );

        encoding.join(domain_clauses);
        let dom = self.domain_encoder.encoding().clone().clone();

        let mut assumptions: IndexMap<EncodingContext, Vec<PLit>> = IndexMap::new();
        for (ctx, enc) in self.encoders.iter_mut() {
            let ts = Instant::now();
            let mut res = enc.encode(bounds, &dom)?;

            let def_lit = ctx.definitional();
            let watcher = ctx.watcher();
            // def_lit -> encoding
            // watcher -> (def_lit -> encoding)
            // Insert the negation of def_lit and watcher into all clauses

            for ref mut clause in res.iter_clauses_mut() {
                clause.push(-watcher);
                if !instance.get_formula().is_conjunctive() {
                    clause.push(-def_lit);
                }
            }

            // Register the assumptions
            for assm in res.assumptions() {
                assumptions.entry(ctx.clone()).or_default().push(assm);
            }
            log::debug!(
                "Encoded: {} ({} clauses, {} ms)",
                ctx.constraint(),
                res.clauses(),
                ts.elapsed().as_millis()
            );
            // Append encoding to results
            encoding.join(res);
            encoding.add_assumption(watcher);
        }
        // Register assumptions
        for (ctx, asms) in assumptions.into_iter() {
            for asm in asms.into_iter() {
                self.register_assumptions(&ctx, &asm);
            }
        }

        Ok(encoding)
    }

    pub fn reset(&mut self) {
        // Reset domain encoder
        self.domain_encoder.reset();
        // Reset encoders
        for (_, en) in self.iter_mut() {
            en.as_mut().reset();
        }
    }

    pub fn construct_model(&self, solver: &cadical::Solver, instance: &Instance) -> Substitution {
        let mut model = Substitution::from(get_str_substitutions(
            self.domain_encoder.encoding(),
            &instance,
            solver,
        ));
        let int_model = Substitution::from(get_int_substitutions(
            self.domain_encoder.encoding(),
            solver,
        ));
        model = model.compose(&int_model);
        // Map variables that were removed in preprocessing to their default value
        model.use_defaults();
        model
    }

    #[allow(dead_code)]
    pub fn print_debug(&self, solver: &cadical::Solver, dom: &DomainEncoding) {
        for (ctx, enc) in self.iter() {
            if solver.value(ctx.definitional).unwrap_or(false) {
                enc.print_debug(solver, dom);
            }
        }
    }

    pub fn num_constraints(&self) -> usize {
        self.contexts.len()
    }

    pub fn iter_mut(
        &mut self,
    ) -> impl Iterator<Item = (&EncodingContext, &mut Box<dyn ConstraintEncoder>)> {
        self.encoders.iter_mut()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&EncodingContext, &Box<dyn ConstraintEncoder>)> {
        self.encoders.iter()
    }
}
