/// Rewrite rules for transforming Boolean nodes.
mod boolean;
mod factors;
mod int;
mod regex;
mod replace;
mod str_int;
mod substr;
mod weq;

use indexmap::IndexMap;

use crate::node::{Node, NodeManager};

#[derive(Debug, Clone, Copy)]
pub enum RewriteRules {
    /* Boolean Rewrites */
    BoolAndConst,
    BoolAndIdem,
    BoolAndComp,
    BoolOrConst,
    BoolOrIdem,
    BoolOrComp,
    BoolNotConst,
    BoolNotDouble,
    EqualityTrivial,

    /* INRE */
    InReConstLhs,
    InReTrivial,
    InReEquation,
    InReConstPrefix,
    InReConstSuffix,
    InRePullComp,

    /* Integers */
    IntFoldConst,
    IntLessTrivial,
    IntGreaterTrivial,
    IntEqTrivial,
    IntDistributeNeg,
    StrLenToAdd,
    ConstStrLen,
    LengthPositive,
    NormalizeLinearIneq,
    NotComparison,

    /* Word Equation Nodes */
    WeqStripLcp,
    WeqStripLcs,
    WeqConstMismatch,
    WeqLengthReasoning,

    /* Factor Constraints */
    PrefixTrivial,
    SuffixTrivial,
    ContainsTrivial,
    FactorOfEmpty,

    /* Substring */
    SubstrConst,
    SubstrNegative,
    AtConst,
    AtNegative,

    /* Replace */
    ReplaceIdem,
    ReplaceInEpsilon,
    ReplaceEpsilon,
    ReplaceSelf,

    /* Str Int Conversion */
    ToIntConstant,
    FromIntConstant,
}

impl RewriteRules {
    pub fn apply(&self, node: &Node, mngr: &mut NodeManager) -> Option<Node> {
        match self {
            RewriteRules::BoolAndConst => boolean::and_const(node, mngr),
            RewriteRules::BoolAndIdem => boolean::and_idem(node, mngr),
            RewriteRules::BoolAndComp => boolean::and_comp(node, mngr),
            RewriteRules::BoolOrConst => boolean::or_const(node, mngr),
            RewriteRules::BoolOrIdem => boolean::or_idem(node, mngr),
            RewriteRules::BoolOrComp => boolean::or_comp(node, mngr),
            RewriteRules::BoolNotConst => boolean::not_const(node, mngr),
            RewriteRules::BoolNotDouble => boolean::not_double_negation(node),
            RewriteRules::EqualityTrivial => boolean::equality_trivial(node, mngr),
            RewriteRules::InReConstLhs => regex::inre_constant_lhs(node, mngr),
            RewriteRules::InReTrivial => regex::inre_trivial(node, mngr),
            RewriteRules::InReEquation => regex::inre_equation(node, mngr),
            RewriteRules::InReConstPrefix => regex::inre_strip_prefix(node, mngr),
            RewriteRules::InReConstSuffix => regex::inre_strip_suffix(node, mngr),
            RewriteRules::InRePullComp => regex::inre_pull_comp(node, mngr),
            RewriteRules::ConstStrLen => int::const_string_length(node, mngr),
            RewriteRules::IntFoldConst => int::fold_constant_ints(node, mngr),
            RewriteRules::IntLessTrivial => int::int_less_trivial(node, mngr),
            RewriteRules::IntGreaterTrivial => int::int_greater_trivial(node, mngr),
            RewriteRules::IntEqTrivial => int::int_equality_trivial(node, mngr),
            RewriteRules::NotComparison => int::not_comparison(node, mngr),
            RewriteRules::IntDistributeNeg => int::distribute_neg(node, mngr),
            RewriteRules::NormalizeLinearIneq => int::normalize_ineq(node, mngr),
            RewriteRules::StrLenToAdd => int::string_length_addition(node, mngr),
            RewriteRules::LengthPositive => int::length_trivial(node, mngr),
            RewriteRules::WeqStripLcp => weq::strip_lcp(node, mngr),
            RewriteRules::WeqStripLcs => weq::strip_lcs(node, mngr),
            RewriteRules::WeqLengthReasoning => weq::length_reasoning(node, mngr),
            RewriteRules::WeqConstMismatch => weq::const_mismatch(node, mngr),
            RewriteRules::PrefixTrivial => factors::trivial_prefixof(node, mngr),
            RewriteRules::SuffixTrivial => factors::trivial_suffixof(node, mngr),
            RewriteRules::ContainsTrivial => factors::trivial_contains(node, mngr),
            RewriteRules::FactorOfEmpty => factors::factor_of_empty_string(node, mngr),
            RewriteRules::SubstrConst => substr::substr_const(node, mngr),
            RewriteRules::SubstrNegative => substr::substr_negative(node, mngr),
            RewriteRules::AtConst => substr::at_const(node, mngr),
            RewriteRules::AtNegative => substr::at_negative(node, mngr),
            RewriteRules::ReplaceIdem => replace::replace_idem(node, mngr),
            RewriteRules::ReplaceInEpsilon => replace::replace_in_epsilon(node, mngr),
            RewriteRules::ReplaceEpsilon => replace::replace_epsilon(node, mngr),
            RewriteRules::ReplaceSelf => replace::replace_self(node, mngr),
            RewriteRules::ToIntConstant => str_int::to_int_constant(node, mngr),
            RewriteRules::FromIntConstant => str_int::from_int_constant(node, mngr),
        }
    }
}

pub struct Rewriter {
    rules: Vec<RewriteRules>,
    rewrite_cache: IndexMap<Node, Node>,
}

impl Rewriter {
    pub fn rewrite(&mut self, node: &Node, max_passes: usize, mngr: &mut NodeManager) -> Node {
        let mut current = node.clone();
        for _ in 0..max_passes {
            let rw = self.pass(&current, mngr);
            if rw == current {
                // nothing changed, return
                break;
            } else {
                // something changed, continue
                current = rw;
            }
        }

        current
    }

    /// Perform a rewrite pass over the given node.
    /// This method applies the rules in the order they were added to the rewriter.
    /// It first applies the rules to the children of the node and then to the node itself.
    /// A single pass calls every rule once for every node in the AST.
    pub fn pass(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        if let Some(cached) = self.rewrite_cache.get(node) {
            return cached.clone();
        }

        // Apply to children first.
        let mut children = Vec::new();
        for child in node.children() {
            children.push(self.pass(child, mngr));
        }

        // Rewrite the current node.
        let mut new_node = mngr.create_node(node.kind().clone(), children);
        for rule in &self.rules {
            if let Some(result) = rule.apply(&new_node, mngr) {
                log::debug!("({:?}): {} -> {}", rule, new_node, result);
                new_node = result;
            }
        }
        self.rewrite_cache.insert(node.clone(), new_node.clone());
        new_node
    }
}

impl Default for Rewriter {
    fn default() -> Self {
        Rewriter {
            rules: REWRITE.iter().copied().collect(),
            rewrite_cache: IndexMap::new(),
        }
    }
}

const REWRITE: &'static [RewriteRules] = &[
    RewriteRules::BoolAndConst,
    RewriteRules::BoolAndIdem,
    RewriteRules::BoolAndComp,
    RewriteRules::BoolOrConst,
    RewriteRules::BoolOrIdem,
    RewriteRules::BoolOrComp,
    RewriteRules::BoolNotConst,
    RewriteRules::BoolNotDouble,
    RewriteRules::EqualityTrivial,
    RewriteRules::InReConstLhs,
    RewriteRules::InReTrivial,
    RewriteRules::InReEquation,
    RewriteRules::InReConstPrefix,
    RewriteRules::InReConstSuffix,
    RewriteRules::InRePullComp,
    RewriteRules::ConstStrLen,
    RewriteRules::NotComparison,
    RewriteRules::NormalizeLinearIneq,
    RewriteRules::IntDistributeNeg,
    RewriteRules::IntFoldConst,
    RewriteRules::IntLessTrivial,
    RewriteRules::IntGreaterTrivial,
    RewriteRules::IntEqTrivial,
    RewriteRules::StrLenToAdd,
    RewriteRules::LengthPositive,
    RewriteRules::WeqStripLcp,
    RewriteRules::WeqStripLcs,
    RewriteRules::WeqConstMismatch,
    RewriteRules::WeqLengthReasoning,
    RewriteRules::PrefixTrivial,
    RewriteRules::SuffixTrivial,
    RewriteRules::ContainsTrivial,
    RewriteRules::FactorOfEmpty,
    RewriteRules::SubstrConst,
    RewriteRules::SubstrNegative,
    RewriteRules::AtConst,
    RewriteRules::AtNegative,
    RewriteRules::ReplaceIdem,
    RewriteRules::ReplaceEpsilon,
    RewriteRules::ReplaceInEpsilon,
    RewriteRules::ReplaceSelf,
    RewriteRules::ToIntConstant,
    RewriteRules::FromIntConstant,
];
