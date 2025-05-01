//! Conversion of nodes into canonical form.

use crate::context::{Sort, Sorted, Variable};
use crate::{
    ast::{Node, NodeKind},
    context::Context,
};

use indexmap::IndexMap;

use smt_str::re::{ReOp, Regex};

use std::rc::Rc;

pub fn canonicalize(node: &Node, ctx: &mut Context) -> Node {
    let mut canonicalizer = Canonicalizer::default();

    canonicalizer.canonicalize(node, ctx)
}

#[derive(Default)]
struct Canonicalizer {
    /// Identities of the form t = v, where t is a term and v is a variable.
    /// Theses dentities are introduced during the canonicalization process if a term is not in canonical form.
    def_identities: IndexMap<Node, Rc<Variable>>,
    cache: IndexMap<Node, Node>,
}

impl Canonicalizer {
    fn canonicalize(&mut self, node: &Node, ctx: &mut Context) -> Node {
        let canonical = self.canonicalize_rec(node, ctx);

        let mut eqs = Vec::with_capacity(self.def_identities.len());
        while !self.def_identities.is_empty() {
            for (n, var) in std::mem::take(&mut self.def_identities).into_iter() {
                let vnode = ctx.ast().variable(var);
                eqs.push(ctx.ast().eq(vnode, n));
            }
        }

        let mut complete = vec![canonical];
        complete.extend(eqs);

        //        let formula = Formula::new(FormulaKind::And(complete), node.clone());
        //        Ok(formula)

        ctx.ast().and(complete)
    }

    /// Brings all literals into canonical form.
    fn canonicalize_rec(&mut self, node: &Node, ctx: &mut Context) -> Node {
        if let Some(f) = self.cache.get(node) {
            return f.clone();
        }
        let canon = if node.is_literal() {
            match self.canonicalize_lit(node, ctx) {
                Some(lit) => lit,
                None => {
                    // Unsupported literal, return the original node
                    node.clone()
                }
            }
        } else if node.is_bool_fun() {
            match node.kind() {
                NodeKind::And | NodeKind::Or => {
                    let rec = node
                        .children()
                        .iter()
                        .map(|c| self.canonicalize_rec(c, ctx))
                        .collect::<Vec<Node>>();
                    let cnode = match node.kind() {
                        NodeKind::And => ctx.ast().and(rec), // FormulaKind::And(rec?),
                        NodeKind::Or => ctx.ast().or(rec),   //FormulaKind::Or(rec?),
                        _ => unreachable!(),
                    };
                    cnode
                    //Ok(Formula::new(kind, node.clone()))
                }
                NodeKind::Not | NodeKind::Imp | NodeKind::Equiv => {
                    panic!("No in NNF: '{}'", node)
                }
                _ => unreachable!("Expected boolean function"),
            }
        } else {
            node.clone()
        };
        self.cache.insert(node.clone(), canon.clone());
        canon
    }

    fn canonicalize_atom(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(node.is_literal());
        debug_assert!(node.is_atomic());
        let atom = match node.kind() {
            NodeKind::Variable(_) | NodeKind::Bool(_) => Some(node.clone()),
            NodeKind::InRe => Some(self.canonicalize_in_re(node, ctx)?),
            NodeKind::Contains => Some(self.canonicalize_contains(node, ctx)?),
            NodeKind::PrefixOf => Some(self.canonicalize_prefixof(node, ctx)?),
            NodeKind::SuffixOf => Some(self.canonicalize_suffixof(node, ctx)?),
            NodeKind::Eq => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap().sort();
                let rhs = node.children().last().unwrap().sort();
                if lhs == rhs {
                    if lhs.is_string() {
                        Some(self.canonicalize_weq(node, ctx)?)
                    } else if lhs.is_int() {
                        Some(self.canonicalize_arithmetic_constraint(node, ctx)?)
                    } else {
                        log::warn!("Unsupported equality constraint: '{}'. ", node);
                        return None;
                    }
                } else {
                    log::warn!(
                        "Unsupported equality constraint: '{}'. Sort mismatch: {} != {}",
                        node,
                        lhs,
                        rhs
                    );
                    return None;
                }
            }
            NodeKind::Gt | NodeKind::Ge | NodeKind::Lt | NodeKind::Le => {
                Some(self.canonicalize_arithmetic_constraint(node, ctx)?)
            }
            _ if node.is_bool_fun() => unreachable!("Expected atomic formula but got '{}'", node),
            _ => None,
        };

        atom
    }

    fn canonicalize_lit(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(node.is_literal());

        if *node.kind() == NodeKind::Not {
            let atom = node.children().first().unwrap();
            let atom_canonical = self.canonicalize_atom(atom, ctx)?;

            match atom.kind() {
                NodeKind::Contains | NodeKind::PrefixOf | NodeKind::SuffixOf => {
                    if let NodeKind::Eq = atom_canonical.kind() {
                        // Unsupported: These introduce universal quantifiers when negated
                        None
                    } else {
                        Some(ctx.ast().not(atom_canonical))
                    }
                }
                _ => Some(ctx.ast().not(atom_canonical)),
            }
        } else {
            let catom = self.canonicalize_atom(node, ctx)?;
            Some(catom)
        }
    }

    fn canonicalize_in_re(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(*node.kind() == NodeKind::InRe);
        debug_assert!(node.children().len() == 2);

        let pat = node.children().first().unwrap();
        let v = if let Some(v) = pat.as_variable() {
            debug_assert!(v.sort().is_string());
            v.clone()
        } else {
            self.define_with_var(pat, ctx)
        };
        let v = ctx.ast().variable(v);
        if let NodeKind::Regex(re) = node[1].kind() {
            if self.re_supported(re) {
                Some(ctx.ast().in_re(v, node[1].clone()))
            } else {
                log::warn!("Unsupported regular expression: '{}'", re);
                None
            }
        } else {
            panic!("Not well-formed: '{}'", node);
        }
    }

    fn re_supported(&mut self, re: &Regex) -> bool {
        // Unuspported if:
        // - Contains a complement anything that is not a range or character
        // - Contains intersection of complement
        fn aux(re: &Regex, in_inter: bool, in_comp: bool) -> bool {
            match re.op() {
                ReOp::Literal(_) | ReOp::Range(_) => true,
                _ if in_comp => false,
                ReOp::None | ReOp::Any | ReOp::All => true,
                ReOp::Concat(rs) | ReOp::Union(rs) => rs.iter().all(|r| aux(r, in_inter, in_comp)),
                ReOp::Inter(rs) => rs.iter().all(|r| aux(r, true, in_comp)),
                ReOp::Star(r) | ReOp::Plus(r) | ReOp::Opt(r) => aux(r, in_inter, in_comp),
                ReOp::Diff(_, _) if in_inter => false,
                ReOp::Diff(r1, r2) => aux(r1, in_inter, in_comp) && aux(r2, in_inter, true),
                ReOp::Comp(_) if in_inter => false,
                ReOp::Comp(r) => aux(r, in_inter, true),
                ReOp::Pow(r, _) | ReOp::Loop(r, _, _) => aux(r, in_inter, in_comp),
            }
        }
        aux(re, false, false)
    }

    fn canonicalize_prefixof(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(*node.kind() == NodeKind::PrefixOf);
        // PrefixOf(r, s) <--> EX t. r = s ++ t
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let prefix = node.children().first().unwrap();
        let of = node.children().last().unwrap();
        // If `prefix`  is constant, then this is a regular expression constraint "of \in prefix.*"
        if prefix.as_str_const().is_some() {
            let v = if let Some(v) = of.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(of, ctx)
            };
            let v = ctx.ast().variable(v);
            Some(ctx.ast().prefix_of(prefix.clone(), v))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = ctx.temp_var(Sort::String);
            let t = ctx.ast().variable(t);
            let rhs = ctx.ast().concat(vec![prefix.clone(), t.clone()]);
            let eq = ctx.ast().eq(of.clone(), rhs);
            self.canonicalize_weq(&eq, ctx)
        }
    }

    fn canonicalize_suffixof(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(*node.kind() == NodeKind::SuffixOf);
        debug_assert!(node.children().len() == 2);

        let suffix = node.children().first().unwrap();
        let of = node.children().last().unwrap();
        // If `s`  is constant, then this is a regular expression constraint r \in .*s
        // These are supported native, only `of` needs to be a single variable in canonical form
        if suffix.as_str_const().is_some() {
            let v = if let Some(v) = of.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(of, ctx)
            };
            let v = ctx.ast().variable(v);
            Some(ctx.ast().suffix_of(suffix.clone(), v))
        } else {
            // Otherwise, rewrite as a word equation: There exists some  u such that  r = t ++ suffix
            let t = ctx.temp_var(Sort::String);
            let t = ctx.ast().variable(t);
            let rhs = ctx.ast().concat(vec![t.clone(), suffix.clone()]);
            let eq = ctx.ast().eq(of.clone(), rhs);
            self.canonicalize_weq(&eq, ctx)
        }
    }

    fn canonicalize_contains(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(*node.kind() == NodeKind::Contains);
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let hay = self.canonicalize_rec(node.children().first().unwrap(), ctx);
        let needle = self.canonicalize_rec(node.children().last().unwrap(), ctx);

        // If `s`  is constant, then this is a regular expression constraint r \in .*s.*
        // These are supported natively and do not require conversion.
        // We only need to ensure that `r` is just a single variable
        if needle.as_str_const().is_some() {
            let v = if let Some(v) = hay.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(&hay, ctx)
            };
            let v = ctx.ast().variable(v);
            Some(ctx.ast().contains(v, needle))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = ctx.temp_var(Sort::String);
            let t = ctx.ast().variable(t);
            let u = ctx.temp_var(Sort::String);
            let u = ctx.ast().variable(u);
            let rhs = ctx.ast().concat(vec![t.clone(), needle.clone(), u.clone()]);
            let eq = ctx.ast().eq(hay.clone(), rhs);
            self.canonicalize_weq(&eq, ctx)
        }
    }

    fn canonicalize_weq(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(*node.kind() == NodeKind::Eq);
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_string());
        debug_assert!(rhs.sort().is_string());
        let lhs = self.canonicalize_string_term(lhs, ctx)?;
        let rhs = self.canonicalize_string_term(rhs, ctx)?;
        Some(ctx.ast().eq(lhs, rhs))
    }

    /// Canocalizes nodes of the form (concat t1 ... tn). The result is a new node (concat r1 ... rm)
    /// where each ri is a einther a (string) variable or a constant. Does the following:
    ///
    /// - If any of node ti is not a variable or a constant, ti is replaced by a new variable ri and the identity ti = ri is stored.
    /// - If ti is a concatenation, it is recursively canonicalized and flattened.
    ///
    /// If the node is a single variable or constant, returns as is
    /// Othwerwise returns a concatenation node
    fn canonicalize_string_term(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        match node.kind() {
            NodeKind::String(_) | NodeKind::Variable(_) => Some(node.clone()),
            NodeKind::Concat => {
                let mut res = Vec::with_capacity(node.children().len());
                for c in node.children() {
                    res.push(self.canonicalize_string_term(c, ctx)?);
                }
                Some(ctx.ast().concat(res))
            }
            _ => {
                let v = self.define_with_var(node, ctx);
                Some(ctx.ast().variable(v))
            }
        }
    }

    fn define_with_var(&mut self, node: &Node, ctx: &mut Context) -> Rc<Variable> {
        let v = if let Some(v) = self.def_identities.get(node) {
            v.clone()
        } else {
            let v = ctx.temp_var(Sort::String);
            self.def_identities.insert(node.clone(), v.clone());
            v
        };
        v
    }

    fn canonicalize_arithmetic_constraint(
        &mut self,
        node: &Node,
        ctx: &mut Context,
    ) -> Option<Node> {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_int() && rhs.sort().is_int());
        // Bring it into the form LHS <> c where c is a constant, <> is one of {<, <=, >, >=, =}
        // and LHS is a linear arithmetic term.

        let lhs = self.canonicalize_linear_arith_term(lhs, ctx)?;
        let rhs = self.canonicalize_linear_arith_term(rhs, ctx)?;

        Some(ctx.ast().create_node(node.kind().clone(), vec![lhs, rhs]))
    }

    /// Takes a node representing a linear arithmetic term and brings it into canonical form.
    /// The canonical form is a sum of terms of the form `c` or `c * v` where c is a constant and v is either an integer variable or the length of a string variable.
    fn canonicalize_linear_arith_term(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(
            node.sort().is_int(),
            "Expected integer term but got '{}'",
            node
        );
        match node.kind() {
            NodeKind::Variable(_) | NodeKind::Int(_) => Some(node.clone()),
            NodeKind::Add | NodeKind::Neg | NodeKind::Sub | NodeKind::Mul => {
                let mut canonical = Vec::with_capacity(node.children().len());
                for ch in node.children() {
                    canonical.push(self.canonicalize_linear_arith_term(ch, ctx)?);
                }
                Some(ctx.ast().create_node(node.kind().clone(), canonical))
            }
            NodeKind::Length => self.canonicalize_string_length(node, ctx),
            _ => None, //panic!("Not well-formed '{}'", node),
        }
    }

    /// Canonicalizes a node of the form (length t), where t is a string term.
    /// If t is equivalent to the form (concat r1 ... rm), the result is a new node (+ (length r1) ... (length rm))
    /// If r1 is a constant word, returns its length as integer instead.
    /// If t is not of this form, returns None
    fn canonicalize_string_length(&mut self, node: &Node, ctx: &mut Context) -> Option<Node> {
        debug_assert!(node.sort().is_int());
        debug_assert!(node.kind() == &NodeKind::Length);
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();
        let pattern = self.canonicalize_string_term(child, ctx)?;
        match pattern.kind() {
            NodeKind::Variable(_) => Some(ctx.ast().str_len(pattern)),
            NodeKind::String(s) => Some(ctx.ast().const_int(s.len() as i64)),
            NodeKind::Concat => {
                let mut ls = Vec::with_capacity(pattern.children().len());
                for ch in pattern.children() {
                    ls.push(ctx.ast().str_len(ch.clone()));
                }
                Some(ctx.ast().add(ls))
            }
            _ => None,
        }
    }
}
