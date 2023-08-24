mod formula;
mod int;

mod string;

use crate::{
    instance::Instance,
    model::{
        formula::{Literal, NNFFormula},
        Substitutable, Substitution,
    },
    preprocess::{
        formula::{ConjunctionSimplifier, FixedAssertions},
        int::{ConstIntReducer, IntSubstitutions},
        string::{
            IndependetVarSubstitutions, RegexConstStrip, SplitPatternRegularConstraints,
            TrivialREReducer,
        },
    },
};

use self::string::{
    WordEquationConstMatching, WordEquationStripPrefixSuffix, WordEquationSubstitutions,
    WordEquationTrivial,
};

/// The result of the application of a preprocessor to a formula.
/// The result can be either:
/// - `Unchanged(f)`: The formula was not changed by the preprocessor.
/// - `Changed(t, s)`: The formula was changed by the preprocessor to `t`, which is equivalent to the original formula.
///                    If the preprocessor applied a substitution `s`, it is returned as well.
///
#[derive(Debug, Clone)]
pub enum PreprocessingResult {
    Changed(NNFFormula),
    Unchanged(NNFFormula),
}

impl PreprocessingResult {
    fn get_formula(&self) -> &NNFFormula {
        match self {
            PreprocessingResult::Changed(f) => f,
            PreprocessingResult::Unchanged(f) => f,
        }
    }
}

impl Substitutable for PreprocessingResult {
    fn apply_substitution(&self, sub: &Substitution) -> Self {
        match self {
            PreprocessingResult::Changed(f) => {
                PreprocessingResult::Changed(f.apply_substitution(sub))
            }
            PreprocessingResult::Unchanged(f) => {
                PreprocessingResult::Changed(f.apply_substitution(sub))
            }
        }
    }
}

trait Preprocessor {
    /// Initialize the preprocessor with the formula to preprocess.
    /// Does not mutate the formula or return a new one.
    /// Can be used for preprocessor-specific initialization.
    fn init(&mut self, _formula: &NNFFormula) {}

    fn apply_literal(
        &mut self,
        literal: Literal,
        _is_asserted: bool,
        _instance: &mut Instance,
    ) -> PreprocessingResult {
        PreprocessingResult::Unchanged(NNFFormula::Literal(literal))
    }

    fn apply_fm(
        &mut self,
        formula: NNFFormula,
        is_asserted: bool,
        _instance: &mut Instance,
    ) -> PreprocessingResult {
        match formula {
            NNFFormula::Literal(l) => self.apply_literal(l, is_asserted, _instance),

            NNFFormula::Or(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    match self.apply_fm(f, false, _instance) {
                        PreprocessingResult::Unchanged(f) => new_fs.push(f),
                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            new_fs.push(f);
                        }
                    }
                }
                let new_fm = NNFFormula::or(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
            NNFFormula::And(fs) => {
                let mut changed = false;
                let mut new_fs = Vec::new();
                for f in fs {
                    match self.apply_fm(f, is_asserted, _instance) {
                        PreprocessingResult::Unchanged(f) => new_fs.push(f),
                        PreprocessingResult::Changed(f) => {
                            changed = true;
                            new_fs.push(f);
                        }
                    }
                }
                let new_fm = NNFFormula::and(new_fs);
                if changed {
                    PreprocessingResult::Changed(new_fm)
                } else {
                    PreprocessingResult::Unchanged(new_fm)
                }
            }
        }
    }

    fn get_substitution(&self) -> Option<Substitution>;

    fn get_name(&self) -> String;

    fn finalize(&mut self, result: PreprocessingResult) -> PreprocessingResult {
        result
    }

    fn apply(&mut self, formula: NNFFormula, _instance: &mut Instance) -> PreprocessingResult {
        let applied = self.apply_fm(formula, true, _instance);

        self.finalize(applied)
    }

    fn new() -> Self
    where
        Self: Sized;
}

pub fn preprocess(instance: &mut Instance) -> (PreprocessingResult, Substitution) {
    let mut comp_sub = Substitution::new();

    //preprocessors.push(Box::new(WordEquationSubstitutions {}));
    let max_rounds = 10;
    let mut preprocessed = PreprocessingResult::Unchanged(instance.get_formula().clone().into());
    for r in 0..max_rounds {
        let mut preprocessors: Vec<Box<dyn Preprocessor>> = vec![
            // Add preprocessors
            Box::new(WordEquationStripPrefixSuffix::new()),
            Box::new(WordEquationConstMatching::new()),
            Box::new(WordEquationTrivial::new()),
            Box::new(WordEquationSubstitutions::new()),
            Box::new(IndependetVarSubstitutions::new()),
            Box::new(ConstIntReducer::new()),
            Box::new(TrivialREReducer::new()),
            Box::new(ConjunctionSimplifier::new()),
            Box::new(IntSubstitutions::new()),
            Box::new(FixedAssertions::new()),
            Box::new(RegexConstStrip::new()),
        ];

        log::trace!("Preprocessing round {}", r);
        let mut rd_changed = false;
        for preprocess in preprocessors.iter_mut() {
            log::trace!("Running Preprocessor: {}", preprocess.get_name());
            preprocess.init(preprocessed.get_formula());
            preprocessed = match preprocessed {
                PreprocessingResult::Changed(f) => match preprocess.apply(f, instance) {
                    PreprocessingResult::Changed(t) => {
                        rd_changed = true;
                        PreprocessingResult::Changed(t)
                    }
                    PreprocessingResult::Unchanged(t) => PreprocessingResult::Changed(t),
                },
                PreprocessingResult::Unchanged(f) => match preprocess.apply(f, instance) {
                    PreprocessingResult::Changed(t) => {
                        rd_changed = true;
                        PreprocessingResult::Changed(t)
                    }
                    PreprocessingResult::Unchanged(t) => PreprocessingResult::Unchanged(t),
                },
            };
            if let Some(sub) = preprocess.get_substitution() {
                if !sub.is_empty() {
                    log::debug!("Applying inferred substitution: {}", sub);
                    preprocessed = preprocessed.apply_substitution(&sub);
                    rd_changed = true;
                    comp_sub = comp_sub.compose(&sub);
                }
            }
        }
        if rd_changed {
            log::debug!("Formula preprocessed to: {}", preprocessed.get_formula());
        } else {
            break;
        }
    }

    // Mandatory normalizer to split regular constraints with compound patterns into a regular constraint with a single variable pattern and a word equation
    let mut normalizer = SplitPatternRegularConstraints::new();
    normalizer.init(preprocessed.get_formula());
    preprocessed = match preprocessed {
        PreprocessingResult::Changed(f) => match normalizer.apply(f, instance) {
            PreprocessingResult::Changed(t) => PreprocessingResult::Changed(t),
            PreprocessingResult::Unchanged(t) => PreprocessingResult::Changed(t),
        },
        PreprocessingResult::Unchanged(f) => match normalizer.apply(f, instance) {
            PreprocessingResult::Changed(t) => PreprocessingResult::Changed(t),
            PreprocessingResult::Unchanged(t) => PreprocessingResult::Unchanged(t),
        },
    };
    if let Some(sub) = normalizer.get_substitution() {
        if !sub.is_empty() {
            log::debug!("Applying inferred substitution: {}", sub);
            preprocessed = preprocessed.apply_substitution(&sub);

            comp_sub = comp_sub.compose(&sub);
        }
    }

    (preprocessed, comp_sub)
}
