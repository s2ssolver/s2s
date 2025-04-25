use std::rc::Rc;

use crate::{
    ast::{Node, NodeKind},
    context::{Sort, Sorted},
};

use super::{
    Atom, LIAConstraint, LIAOp, LIATerm, LinearSummand, Literal, Pattern, RegularConstraint,
    RegularFactorConstraint, Symbol, WordEquation,
};

/// Converts an AST [Node] into an IR [Literal].
/// Assumes that the formula is in NNF, meaning, if a `Not` node is found, the polarity is negative, otherwise positive.
/// If the node does not represent a first-order literal has not corresponding IR representation, returns None.
pub fn convert(ast: &Node) -> Option<Literal> {
    match ast.kind() {
        NodeKind::Bool(true) => Some(Literal::positive(Rc::new(Atom::True))),
        NodeKind::Bool(false) => Some(Literal::positive(Rc::new(Atom::False))),
        NodeKind::Variable(v) if v.sort().is_bool() => {
            Some(Literal::positive(Rc::new(Atom::Boolvar(v.clone()))))
        }
        NodeKind::Not => {
            let inner = convert(&ast.children()[0])?;
            Some(inner.flip_polarity())
        }
        NodeKind::Eq if ast.children().len() == 2 => {
            let atom = match (ast.children()[0].sort(), ast.children()[1].sort()) {
                (Sort::Int, Sort::Int) => convert_lia(ast)?,
                (Sort::String, Sort::String) => convert_weq(ast)?,
                _ => return None,
            };
            Some(Literal::positive(Rc::new(atom)))
        }
        NodeKind::InRe if ast.children().len() == 2 => {
            let inre = Rc::new(convert_inre(&ast.children()[0], &ast.children()[1])?);
            Some(Literal::positive(inre))
        }
        NodeKind::PrefixOf if ast.children().len() == 2 => {
            let prefixof = Rc::new(convert_reg_prefixof(
                &ast.children()[0],
                &ast.children()[1],
            )?);
            Some(Literal::positive(prefixof))
        }
        NodeKind::SuffixOf if ast.children().len() == 2 => {
            let suffixof = Rc::new(convert_reg_suffixof(
                &ast.children()[0],
                &ast.children()[1],
            )?);
            Some(Literal::positive(suffixof))
        }
        NodeKind::Contains if ast.children().len() == 2 => {
            let contains = Rc::new(convert_reg_contains(
                &ast.children()[0],
                &ast.children()[1],
            )?);
            Some(Literal::positive(contains))
        }
        NodeKind::Lt | NodeKind::Le | NodeKind::Ge | NodeKind::Gt => {
            let atom = convert_lia(ast)?;
            Some(Literal::positive(Rc::new(atom)))
        }
        _ => None,
    }
}

/// Converts a node represing a linear integer arithmetic constraint to an [LIAConstraint].
fn convert_lia(n: &Node) -> Option<Atom> {
    debug_assert_eq!(n.children().len(), 2);
    let l = &n.children()[0];
    let r = &n.children()[1];

    let lhs = convert_lia_term(l)?;
    let rhs = convert_lia_term(r)?;
    let op = match n.kind() {
        NodeKind::Lt => LIAOp::Less,
        NodeKind::Le => LIAOp::Leq,
        NodeKind::Eq => LIAOp::Eq,
        NodeKind::Ge => LIAOp::Geq,
        NodeKind::Gt => LIAOp::Greater,
        _ => return None,
    };
    let constraint = normalize_lia_constraint(lhs, op, rhs);
    Some(Atom::Linear(constraint))
}

fn convert_weq(n: &Node) -> Option<Atom> {
    debug_assert_eq!(n.children().len(), 2);
    debug_assert_eq!(*n.kind(), NodeKind::Eq);
    let l = &n.children()[0];
    let r = &n.children()[1];
    if !l.sort().is_string() || !r.sort().is_string() {
        return None;
    }
    let lhs = convert_pattern(l)?;
    let rhs = convert_pattern(r)?;
    Some(Atom::WordEquation(WordEquation::new(lhs, rhs)))
}

/// Converts a node representing a regular constaint into an Atom of type RegularConstraint
fn convert_inre(left: &Node, right: &Node) -> Option<Atom> {
    if let NodeKind::Regex(re) = right.kind() {
        let pat = convert_pattern(left)?;
        let inre = RegularConstraint::new(Rc::new(pat), re.clone());
        Some(Atom::InRe(inre))
    } else {
        None
    }
}

/// Converts a prefix_of node.
/// If the node is a regular prefixof (constant prefix), returns an atom of type [RegularFactorConstraint].
fn convert_reg_prefixof(prefix: &Node, of: &Node) -> Option<Atom> {
    let of = convert_pattern(of)?;
    let prefix = convert_pattern(prefix)?;
    if let Some(prefix) = prefix.as_constant() {
        let c = Atom::FactorConstraint(RegularFactorConstraint::prefix(Rc::new(of), prefix));
        Some(c)
    } else {
        None
    }
}
/// Converts a suffix_of node.
/// If the node is a regular suffix of (constant suffix), returns an atom of type [RegularFactorConstraint].
fn convert_reg_suffixof(prefix: &Node, of: &Node) -> Option<Atom> {
    let of = convert_pattern(of)?;
    let suffix = convert_pattern(prefix)?;
    if let Some(suffix) = suffix.as_constant() {
        let c = Atom::FactorConstraint(RegularFactorConstraint::suffix(Rc::new(of), suffix));
        Some(c)
    } else {
        None
    }
}

/// Converts a contains node.
/// If the node is a regular contains (constant needle), returns an atom of type [RegularFactorConstraint].
fn convert_reg_contains(hay: &Node, needle: &Node) -> Option<Atom> {
    let needle = convert_pattern(needle)?;
    let hay = convert_pattern(hay)?;
    if let Some(needle) = needle.as_constant() {
        let c = Atom::FactorConstraint(RegularFactorConstraint::contains(Rc::new(hay), needle));
        Some(c)
    } else {
        None
    }
}

/// Converts a node represinting a pattern to a [Pattern].
fn convert_pattern(node: &Node) -> Option<Pattern> {
    let mut res = Pattern::empty();
    match node.kind() {
        NodeKind::String(s) => res.push_word(s),
        NodeKind::Variable(v) if v.sort().is_string() => res.push_var(v.clone()),
        NodeKind::Concat => {
            for r in node.children() {
                res.extend(convert_pattern(r)?);
            }
        }
        _ => return None,
    };
    Some(res)
}

/// Converts a node representing a Linear Arithmetic Term to an [LIATerm].
fn convert_lia_term(node: &Node) -> Option<LIATerm> {
    match node.kind() {
        NodeKind::Variable(v) => {
            if v.sort().is_int() {
                Some(LIATerm::from_var(v.clone()))
            } else {
                panic!("Expected integer variable but got '{}'", v)
            }
        }
        NodeKind::Int(i) => Some(LIATerm::from_const(*i)),
        NodeKind::Add => {
            let mut sum = LIATerm::new();
            for c in node.children() {
                let canonical = convert_lia_term(c)?;
                sum.add(canonical);
            }
            Some(sum)
        }
        NodeKind::Neg => {
            // Intepret as (-1)*Inner
            let mut converted = convert_lia_term(&node.children()[0])?;
            converted.multiply_constant(-1);
            Some(converted)
        }
        NodeKind::Sub => {
            // rewrite (- t1 t2 ... tn) as (+ t1 (- t2)... (- tn))
            debug_assert!(node.children().len() > 1);
            let mut res = LIATerm::new();
            for (i, ch) in node.children().iter().enumerate() {
                let conv = convert_lia_term(ch)?;
                if i == 0 {
                    res.add(conv);
                } else {
                    res.sub(conv);
                }
            }
            Some(res)
        }
        NodeKind::Mul => {
            // distribute the multiplication, abort if we have non-linear terms
            let mut res = LIATerm::from_const(1);
            for e in node.children() {
                let conv = convert_lia_term(e)?;
                res = LIATerm::multiply(res, conv)?;
            }
            Some(res)
        }
        NodeKind::Length => string_length(node),
        _ => None, //panic!("Not well-formed '{}'", node),
    }
}

/// Convers a node representing length of a string to a [LIATerm].
fn string_length(n: &Node) -> Option<LIATerm> {
    let of = &n[0];
    let patt = convert_pattern(of)?;
    let mut res = LIATerm::new();
    for s in patt.symbols() {
        let t = match s {
            Symbol::Constant(_) => LIATerm::from_const(1),
            Symbol::Variable(v) => LIATerm::from_var_len(v.clone()),
        };
        res.add(t);
    }

    Some(res)
}

/// Normalizes a linear arithmetic constraint of the form `left # right` where
///
/// - `left` and `right` are [LIATerm]s
/// - `#` is a [LIAOp]
///
///  by and returns [LIAConstraint].
fn normalize_lia_constraint(l: LIATerm, op: LIAOp, r: LIATerm) -> LIAConstraint {
    let mut lhs = LIATerm::new();
    let mut rhs = 0;

    for s in l.into_summands() {
        match &s {
            LinearSummand::Mult(_, _) => lhs.add_summand(s),
            LinearSummand::Const(c) => rhs -= c,
        }
    }
    for s in r.into_summands() {
        match s {
            LinearSummand::Mult(v, c) => lhs.add_summand(LinearSummand::Mult(v, -c)),
            LinearSummand::Const(c) => rhs += c,
        }
    }

    lhs.canonicalize();
    LIAConstraint::new(lhs, op, rhs)
}
