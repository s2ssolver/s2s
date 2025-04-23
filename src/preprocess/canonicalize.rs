//! Conversion of nodes into canonical form.
//! TODO: This needs major refactoring.

use crate::ast::{
    canonical::{
        ArithOperator, Atom, AtomKind, LinearArithTerm, LinearConstraint, LinearSummand, Literal,
        Pattern, RegularConstraint, RegularFactorConstraint, Symbol, WordEquation,
    },
    Node, NodeKind, NodeManager,
};
use crate::context::{Sort, Sorted, Variable};

use indexmap::IndexMap;

use smt_str::re::{ReOp, Regex};

use std::rc::Rc;

pub fn canonicalize(node: &Node, mngr: &mut NodeManager) -> Node {
    let mut canonicalizer = Canonicalizer::default();

    canonicalizer.canonicalize(node, mngr)
}

#[derive(Default)]
struct Canonicalizer {
    /// Identities of the form t = v, where t is a term and v is a variable.
    /// Theses dentities are introduced during the canonicalization process if a term is not in canonical form.
    def_identities: IndexMap<Node, Rc<Variable>>,
    patterns: IndexMap<Node, Pattern>,
    cache: IndexMap<Node, Node>,
}

impl Canonicalizer {
    fn canonicalize(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        let canonical = self.canonicalize_rec(node, mngr);

        let mut eqs = Vec::with_capacity(self.def_identities.len());
        while !self.def_identities.is_empty() {
            for (n, var) in std::mem::take(&mut self.def_identities).into_iter() {
                if let Some(rhs) = self.canonicalize_concat(n.clone(), mngr) {
                    let lhs = Pattern::variable(var.clone());
                    let weq = WordEquation::new(lhs, rhs);
                    let atom = mngr.atom(AtomKind::WordEquation(weq));
                    let lit = Literal::new(true, atom);
                    let node = mngr.literal(lit);
                    eqs.push(node);
                } else {
                    let vnode = mngr.var(var);
                    eqs.push(mngr.eq(vnode, n));
                }
            }
        }

        let mut complete = vec![canonical];
        complete.extend(eqs);

        //        let formula = Formula::new(FormulaKind::And(complete), node.clone());
        //        Ok(formula)

        mngr.and(complete)
    }

    /// Brings all literals into canonical form.
    fn canonicalize_rec(&mut self, node: &Node, mngr: &mut NodeManager) -> Node {
        if let Some(f) = self.cache.get(node) {
            return f.clone();
        }
        let canon = if node.is_literal() {
            match self.canonicalize_lit(node, mngr) {
                Some(lit) => mngr.literal(lit),
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
                        .map(|c| self.canonicalize_rec(c, mngr))
                        .collect::<Vec<Node>>();
                    let cnode = match node.kind() {
                        NodeKind::And => mngr.and(rec), // FormulaKind::And(rec?),
                        NodeKind::Or => mngr.or(rec),   //FormulaKind::Or(rec?),
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

    fn canonicalize_atom(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(node.is_literal());
        debug_assert!(node.is_atomic());
        let atom = match node.kind() {
            NodeKind::Variable(v) => {
                debug_assert!(v.sort().is_bool());
                Some(mngr.atom(AtomKind::Boolvar(v.clone())))
            }
            NodeKind::Bool(_) => None,
            NodeKind::InRe => Some(self.canonicalize_in_re(node, mngr)?),
            NodeKind::Contains => Some(self.canonicalize_contains(node, mngr)?),
            NodeKind::PrefixOf => Some(self.canonicalize_prefixof(node, mngr)?),
            NodeKind::SuffixOf => Some(self.canonicalize_suffixof(node, mngr)?),
            NodeKind::Eq => {
                debug_assert!(node.children().len() == 2);
                let lhs = node.children().first().unwrap().sort();
                let rhs = node.children().last().unwrap().sort();
                if lhs == rhs {
                    if lhs.is_string() {
                        Some(self.canonicalize_weq(node, mngr)?)
                    } else if lhs.is_int() {
                        Some(self.canonicalize_arithmetic_constraint(node, mngr)?)
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
                Some(self.canonicalize_arithmetic_constraint(node, mngr)?)
            }
            _ if node.is_bool_fun() => unreachable!("Expected atomic formula but got '{}'", node),
            _ => None,
        };

        atom
    }

    fn canonicalize_lit(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Literal> {
        debug_assert!(node.is_literal());

        if *node.kind() == NodeKind::Not {
            let atom = node.children().first().unwrap();
            let catom = self.canonicalize_atom(atom, mngr)?;

            match atom.kind() {
                NodeKind::Contains | NodeKind::PrefixOf | NodeKind::SuffixOf
                    if !matches!(catom.kind(), AtomKind::FactorConstraint(_)) =>
                {
                    // Unsupported: These introduce universal quantifiers when negated
                    None
                }
                _ => Some(Literal::new(false, catom)),
            }
        } else {
            let catom = self.canonicalize_atom(node, mngr)?;
            Some(Literal::new(true, catom))
        }
    }

    fn canonicalize_in_re(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(*node.kind() == NodeKind::InRe);
        debug_assert!(node.children().len() == 2);

        let pat = node.children().first().unwrap();
        let v = if let Some(v) = pat.as_variable() {
            debug_assert!(v.sort().is_string());
            v.clone()
        } else {
            self.define_with_var(pat, mngr)
        };
        if let NodeKind::Regex(re) = node[1].kind() {
            if self.re_supported(re) {
                let atom = AtomKind::InRe(RegularConstraint::new(v, re.clone()));
                Some(mngr.atom(atom))
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

    fn canonicalize_prefixof(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(*node.kind() == NodeKind::PrefixOf);
        // PrefixOf(r, s) <--> EX t. r = s ++ t
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let prefix = node.children().first().unwrap();
        let of = node.children().last().unwrap();
        // If `prefix`  is constant, then this is a regular expression constraint "of \in prefix.*"
        if let Some(constprefix) = prefix.as_str_const() {
            let v = if let Some(v) = of.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(of, mngr)
            };
            Some(
                mngr.atom(AtomKind::FactorConstraint(RegularFactorConstraint::prefix(
                    v,
                    constprefix.clone(),
                ))),
            )
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![prefix.clone(), t.clone()]);
            let eq = mngr.eq(of.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_suffixof(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(*node.kind() == NodeKind::SuffixOf);
        debug_assert!(node.children().len() == 2);

        let suffix = node.children().first().unwrap();
        let of = node.children().last().unwrap();
        // If `s`  is constant, then this is a regular expression constraint r \in .*s
        if let Some(s) = suffix.as_str_const() {
            let v = if let Some(v) = of.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(of, mngr)
            };
            Some(
                mngr.atom(AtomKind::FactorConstraint(RegularFactorConstraint::suffix(
                    v,
                    s.clone(),
                ))),
            )
        } else {
            // Otherwise, rewrite as a word equation: There exists some  u such that  r = t ++ suffix
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let rhs = mngr.concat(vec![t.clone(), suffix.clone()]);
            let eq = mngr.eq(of.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_contains(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(*node.kind() == NodeKind::Contains);
        debug_assert!(node.children().len() == 2);
        // Contains(r, s) <--> r contains s

        let container = self.canonicalize_rec(node.children().first().unwrap(), mngr);
        let contained = self.canonicalize_rec(node.children().last().unwrap(), mngr);

        // If `s`  is constant, then this is a regular expression constraint r \in .*s.*
        if let Some(s) = contained.as_str_const() {
            let v = if let Some(v) = container.as_variable() {
                debug_assert!(v.sort().is_string());
                v.clone()
            } else {
                self.define_with_var(&container, mngr)
            };
            Some(mngr.atom(AtomKind::FactorConstraint(
                RegularFactorConstraint::contains(v, s.clone()),
            )))
        } else {
            // Otherwise, rewrite as a word equation: There exists some t, u such that  r = t ++ s ++ u
            let t = mngr.temp_var(Sort::String);
            let t = mngr.var(t);
            let u = mngr.temp_var(Sort::String);
            let u = mngr.var(u);
            let rhs = mngr.concat(vec![t.clone(), contained.clone(), u.clone()]);
            let eq = mngr.eq(container.clone(), rhs);
            self.canonicalize_weq(&eq, mngr)
        }
    }

    fn canonicalize_weq(&mut self, node: &Node, mngr: &mut NodeManager) -> Option<Rc<Atom>> {
        debug_assert!(*node.kind() == NodeKind::Eq);
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_string());
        debug_assert!(rhs.sort().is_string());
        let lhs = self.canonicalize_concat(lhs.clone(), mngr)?;
        let rhs = self.canonicalize_concat(rhs.clone(), mngr)?;
        let weq = WordEquation::new(lhs, rhs);
        Some(mngr.atom(AtomKind::WordEquation(weq)))
    }

    /// Canocalizes nodes of the form (concat t1 ... tn). The result is a new node (concat r1 ... rm)
    /// where each ri is a einther a (string) variable or a constant. Does the following:
    ///
    /// - If any of node ti is not a variable or a constant, ti is replaced by a new variable ri and the identity ti = ri is stored.
    /// - If ti is a concatenation, it is recursively canonicalized and flattened.
    ///
    /// Returns a Pattern representing the canonical form of the concatenation.
    fn canonicalize_concat(&mut self, node: Node, mngr: &mut NodeManager) -> Option<Pattern> {
        if let Some(p) = self.patterns.get(&node) {
            return Some(p.clone());
        }

        if !(*node.kind() == NodeKind::Concat || node.is_var() || node.is_const()) {
            return None;
        }

        if let Some(v) = node.as_variable() {
            Some(Pattern::variable(v.clone()))
        } else if let Some(s) = node.as_str_const() {
            Some(Pattern::constant(s.clone()))
        } else if *node.kind() == NodeKind::Concat {
            let mut rec = Pattern::empty();
            for c in node.children() {
                let canon = self.canonicalize_concat(c.clone(), mngr)?;
                rec.extend(canon);
            }
            self.patterns.insert(node.clone(), rec.clone());
            Some(rec)
        } else {
            // define a new variable for the node
            debug_assert!(node.sort().is_string());
            let v = self.define_with_var(&node, mngr);
            Some(Pattern::variable(v))
        }
    }

    fn define_with_var(&mut self, node: &Node, mngr: &mut NodeManager) -> Rc<Variable> {
        let v = if let Some(v) = self.def_identities.get(node) {
            v.clone()
        } else {
            let v = mngr.temp_var(Sort::String);
            self.def_identities.insert(node.clone(), v.clone());
            v
        };
        v
    }

    fn canonicalize_arithmetic_constraint(
        &mut self,
        node: &Node,
        mngr: &mut NodeManager,
    ) -> Option<Rc<Atom>> {
        debug_assert!(node.children().len() == 2);
        let lhs = node.children().first().unwrap();
        let rhs = node.children().last().unwrap();
        debug_assert!(lhs.sort().is_int() && rhs.sort().is_int());
        // Bring it into the form LHS <> c where c is a constant, <> is one of {<, <=, >, >=, =}
        // and LHS is a linear arithmetic term.

        let lhs = self.canonicalize_linear_arith_term(lhs.clone(), mngr)?;
        let rhs = self.canonicalize_linear_arith_term(rhs.clone(), mngr)?;
        let (clhs, crhs) = self.normalize_linear(lhs, rhs);

        let op = match node.kind() {
            NodeKind::Eq => ArithOperator::Eq,
            NodeKind::Lt => ArithOperator::Less,
            NodeKind::Le => ArithOperator::Leq,
            NodeKind::Gt => ArithOperator::Greater,
            NodeKind::Ge => ArithOperator::Geq,
            _ => unreachable!("Not a linear constraint"),
        };
        let mut lc = LinearConstraint::new(clhs, op, crhs);
        lc.canonicalize();

        Some(mngr.atom(AtomKind::Linear(lc)))
    }

    /// Takes a node representing a linear arithmetic term and brings it into canonical form.
    /// The canonical form is a sum of terms of the form `c` or `c * v` where c is a constant and v is either an integer variable or the length of a string variable.
    fn canonicalize_linear_arith_term(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Option<LinearArithTerm> {
        debug_assert!(
            node.sort().is_int(),
            "Expected integer term but got '{}'",
            node
        );
        match node.kind() {
            NodeKind::Variable(v) => {
                if v.sort().is_int() {
                    Some(LinearArithTerm::from_var(v.clone()))
                } else {
                    panic!("Expected integer variable but got '{}'", v)
                }
            }
            NodeKind::Int(i) => Some(LinearArithTerm::from_const(*i)),
            NodeKind::Add => {
                let mut sum = LinearArithTerm::new();
                for c in node.children() {
                    let canonical = self.canonicalize_linear_arith_term(c.clone(), mngr)?;
                    sum.add(canonical);
                }
                Some(sum)
            }
            NodeKind::Neg => {
                debug_assert!(node.children().len() == 1);
                // rewrite (- t) as (-1 * t)
                debug_assert!(node.children().len() == 1);
                let ch = node.children().first().unwrap();
                debug_assert!(ch.sort().is_int());
                let negone = mngr.const_int(-1);
                let as_mult = mngr.mul(vec![negone, ch.clone()]);
                self.canonicalize_linear_arith_term(as_mult, mngr)
            }
            NodeKind::Sub => {
                // rewrite (- t1 t2 ... tn) as (+ t1 (- t2)... (- tn))
                debug_assert!(node.children().len() > 1);
                let norm = node
                    .children()
                    .iter()
                    .enumerate()
                    .map(|(i, s)| {
                        if i == 0 {
                            s.clone()
                        } else {
                            mngr.neg(s.clone())
                        }
                    })
                    .collect();
                let as_addition = mngr.add(norm);
                self.canonicalize_linear_arith_term(as_addition, mngr)
            }
            NodeKind::Mul => {
                // distribute the multiplication, abort if we have non-linear terms
                let mut res = LinearArithTerm::from_const(1);
                for e in node.children() {
                    let next = self.canonicalize_linear_arith_term(e.clone(), mngr)?;
                    res = match LinearArithTerm::multiply(res, next) {
                        Some(r) => r,
                        None => {
                            panic!("Non-linear term in multiplication: '{}'", node)
                        }
                    }
                }
                Some(res)
            }
            NodeKind::Length => self.canonicalize_string_length(node, mngr),
            _ => None, //panic!("Not well-formed '{}'", node),
        }
    }

    /// Canonicalizes a node of the form (length t), where t is a string term.
    /// If t is of the form (concat r1 ... rm), the result is a new node (+ (length r1) ... (length rm))
    /// If t is a variable, the result is the same node.
    /// If t is a constant, the result is a new node with the constant length.
    fn canonicalize_string_length(
        &mut self,
        node: Node,
        mngr: &mut NodeManager,
    ) -> Option<LinearArithTerm> {
        debug_assert!(node.sort().is_int());
        debug_assert!(node.kind() == &NodeKind::Length);
        debug_assert!(node.children().len() == 1);
        let child = node.children().first().unwrap();
        match child.kind() {
            NodeKind::String(s) => {
                let len = s.len() as i64;
                Some(LinearArithTerm::from_const(len))
            }
            NodeKind::Variable(v) => {
                if v.sort().is_string() {
                    Some(LinearArithTerm::from_var_len(v.clone()))
                } else {
                    panic!("Expected string variable but got '{}'", v)
                }
            }
            NodeKind::Concat => {
                let canonical = self.canonicalize_concat(child.clone(), mngr)?;
                let mut res = LinearArithTerm::from_const(0);
                for c in canonical.symbols() {
                    let add = match c {
                        Symbol::Constant(_) => LinearArithTerm::from_const(1),
                        Symbol::Variable(rc) => LinearArithTerm::from_var_len(rc.clone()),
                    };
                    res.add(add);
                }
                Some(res)
            }
            _ => None, //panic!("Not well-formed '{}'", node),
        }
    }

    fn normalize_linear(
        &self,
        lhs: LinearArithTerm,
        rhs: LinearArithTerm,
    ) -> (LinearArithTerm, i64) {
        let mut new_lhs = LinearArithTerm::new();
        let mut rhs_const = 0;
        for term in lhs.into_summands() {
            match &term {
                LinearSummand::Const(c) => rhs_const -= c,
                LinearSummand::Mult(_, _) => new_lhs.add_summand(term),
            }
        }
        for term in rhs.into_summands() {
            match &term {
                LinearSummand::Const(c) => rhs_const += c,
                LinearSummand::Mult(_, _) => new_lhs.add_summand(term.flip_sign()),
            }
        }
        (new_lhs, rhs_const)
    }
}
