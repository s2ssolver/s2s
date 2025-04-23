use smallvec::smallvec;
use smt_str::re::Regex;

use super::*;
use crate::ast::{Node, NodeKind, NodeManager};

/// Folds `to_int(s)` where `s` is a constant string to an integer constant.
#[derive(Debug, Clone, Copy)]
pub(super) struct ToIntConstant;
impl EquivalenceRule for ToIntConstant {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if let NodeKind::ToInt = *node.kind() {
            let ch = node.children().first().unwrap();
            if let Some(s) = ch.as_str_const() {
                if s.is_empty() {
                    return Some(mngr.const_int(-1));
                }
                let i = s.to_string().parse::<i64>().unwrap_or(-1);
                return Some(mngr.const_int(i));
            }
        }
        None
    }
}

/// Folds `from_int(i)` where `i` is a constant integer to a string constant.
#[derive(Debug, Clone, Copy)]
pub(super) struct FromIntConstant;
impl EquivalenceRule for FromIntConstant {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if let NodeKind::FromInt = *node.kind() {
            let ch = node.children().first().unwrap();
            if let Some(i) = ch.as_int_const() {
                if i >= 0 {
                    return Some(mngr.const_str(&i.to_string()));
                } else {
                    return Some(mngr.empty_string());
                }
            }
        }
        None
    }
}

/// Finds `q*(str.to_int x) = c` where
///
/// -`x` is a variable,
/// - `p`, `c` are a constant integers such that `c/p` is a non-neative integer
///
/// Replace the node with
///
/// - `x in R` where `R is the regular expression that matches the string represenation of `c/p` prefixed by an arbitrary number of zeros, if `p | c`
/// - `false` otherwise
#[derive(Debug, Clone, Copy)]
pub(super) struct VarEqConstantToInt;
impl EquivalenceRule for VarEqConstantToInt {
    fn apply(&self, node: &Node, _: &IndexSet<Node>, mngr: &mut NodeManager) -> Option<Node> {
        if let NodeKind::Eq = *node.kind() {
            let lhs = node.children().first().unwrap();
            let rhs = node.children().last().unwrap();
            let (s, v, r) = match (lhs.kind(), rhs.kind()) {
                (NodeKind::Mul, NodeKind::Int(i)) => {
                    let mul_lhs = &lhs.children()[0];
                    let mul_rhs = &lhs.children()[1];
                    let (v, s) = match (mul_lhs.kind(), mul_rhs.kind()) {
                        (NodeKind::ToInt, NodeKind::Int(s)) => {
                            if let NodeKind::Variable(v) =
                                mul_lhs.children().first().unwrap().kind()
                            {
                                (v, s)
                            } else {
                                return None;
                            }
                        }
                        (NodeKind::Int(s), NodeKind::ToInt) => {
                            if let NodeKind::Variable(v) =
                                mul_rhs.children().first().unwrap().kind()
                            {
                                (v, s)
                            } else {
                                return None;
                            }
                        }
                        _ => return None,
                    };
                    (*s, v.clone(), *i)
                }
                (NodeKind::ToInt, NodeKind::Int(s)) => {
                    if let NodeKind::Variable(v) = lhs.children().first().unwrap().kind() {
                        (1, v.clone(), *s)
                    } else {
                        return None;
                    }
                }
                (NodeKind::Int(s), NodeKind::ToInt) => {
                    if let NodeKind::Variable(v) = rhs.children().first().unwrap().kind() {
                        (1, v.clone(), *s)
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };

            let rhs = r / s;
            if rhs < 0 {
                return None;
            }

            // if it evenly divides, create the regex, otherwise return false
            if r % s == 0 {
                let re = int_to_re(rhs as u64, mngr);

                // cast to node
                let re = mngr.const_regex(re);

                let vnode = mngr.var(v);

                return Some(mngr.in_re(vnode, re));
            } else {
                return Some(mngr.ffalse());
            }
        }
        None
    }
}

/// Converts an integer to a regular expression that matches the string representation of the integer prefixed by an arbitrary number of zeros.
/// For example, `int_to_re(4)` returns the regular expression `0*4`.
fn int_to_re(i: u64, mngr: &mut NodeManager) -> Regex {
    let zero = mngr.re_builder().to_re("0".into());
    let zero_star = mngr.re_builder().star(zero);

    let as_str = i.to_string();
    let as_str_re = mngr.re_builder().to_re(as_str.into());
    // 0*as_str
    mngr.re_builder().concat(smallvec![zero_star, as_str_re])
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use crate::{
        ast::NodeManager,
        context::Sort,
        preprocess::simp::{str_int::VarEqConstantToInt, EquivalenceRule},
    };

    use super::int_to_re;

    #[test]
    fn test_var_to_int_eq_constant() {
        // to_int(x) = 4
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());

        let to_int = mngr.str_to_int(x_node.clone());
        let four = mngr.const_int(4);

        let eq = mngr.eq(to_int, four.clone());

        let re = int_to_re(4, &mut mngr);
        let re = mngr.const_regex(re);
        let expected = mngr.in_re(x_node, re);

        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, Some(expected));
    }

    #[test]
    fn test_var_to_int_eq_constant_scaled() {
        // 2*to_int(x) = 4
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());
        let two = mngr.const_int(2);

        let to_int = mngr.str_to_int(x_node.clone());
        let scaled = mngr.mul(vec![two.clone(), to_int]);
        let four = mngr.const_int(4);

        let eq = mngr.eq(scaled, four.clone());

        let re = int_to_re(2, &mut mngr);
        let re = mngr.const_regex(re);
        let expected = mngr.in_re(x_node, re);

        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, Some(expected));
    }

    #[test]
    fn test_var_to_int_eq_constant_scaled_neg() {
        // -2*to_int(x) = -4
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());
        let two = mngr.const_int(-2);

        let to_int = mngr.str_to_int(x_node.clone());
        let scaled = mngr.mul(vec![two.clone(), to_int]);
        let four = mngr.const_int(-4);

        let eq = mngr.eq(scaled, four.clone());

        let re = int_to_re(2, &mut mngr);
        let re = mngr.const_regex(re);
        let expected = mngr.in_re(x_node, re);

        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, Some(expected));
    }

    #[test]
    fn test_var_to_int_eq_constant_scaled_unsat() {
        // 2*to_int(x) = 5
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());
        let two = mngr.const_int(2);

        let to_int = mngr.str_to_int(x_node.clone());
        let scaled = mngr.mul(vec![two.clone(), to_int]);
        let four = mngr.const_int(5);

        let eq = mngr.eq(scaled, four.clone());

        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, Some(mngr.ffalse()));
    }

    #[test]
    fn test_var_to_int_eq_constant_scaled_neg_invalid() {
        // -2*to_int(x) = 5
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());
        let two = mngr.const_int(-2);

        let to_int = mngr.str_to_int(x_node.clone());
        let scaled = mngr.mul(vec![two.clone(), to_int]);
        let four = mngr.const_int(5);

        let eq = mngr.eq(scaled, four.clone());
        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, None);
    }

    #[test]
    fn test_var_to_int_eq_constant_scaled_neg_invalid_2() {
        // -2*to_int(x) = 5
        let mut mngr = NodeManager::default();
        let x = mngr.temp_var(Sort::String);
        let x_node = mngr.var(x.clone());
        let two = mngr.const_int(2);

        let to_int = mngr.str_to_int(x_node.clone());
        let scaled = mngr.mul(vec![two.clone(), to_int]);
        let four = mngr.const_int(-5);

        let eq = mngr.eq(scaled, four.clone());

        let got = VarEqConstantToInt.apply(&eq, &IndexSet::new(), &mut mngr);
        assert_eq!(got, None);
    }
}
