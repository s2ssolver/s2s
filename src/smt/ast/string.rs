use std::fmt::Display;

use crate::smt::{convert_smtlib_char, Sort, Symbol};

use super::{AstNode, Expression};

/// The SMT-LIB string expressions.
/// Note that these comprise the operations defined in the SMT-LIB theory of strings.
/// Not all expression are necessarily of sort String.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum StrExpr {
    /// A string variable
    Var(Symbol),
    /// A string constant
    Constant(String),
    /// Concatenation
    Concat(Vec<Expression>),
    /// Length
    Length(Expression),
    InRe(Expression, Expression),
    /// Substring
    Substr(Expression, Expression, Expression),
    /// String at
    At(Expression, Expression),
    /// Prefix
    PrefixOf(Expression, Expression),
    /// Suffix
    SuffixOf(Expression, Expression),
    /// Contains
    Contains(Expression, Expression),
    /// Index of
    IndexOf(Expression, Expression, Expression),
    /// Replace
    Replace(Expression, Expression, Expression),
    /// Replace all
    ReplaceAll(Expression, Expression, Expression),
    /// Replace re
    ReplaceRe(Expression, Expression, Expression),
    /// Replace re all
    ReplaceReAll(Expression, Expression, Expression),
    /// To integer
    ToInt(Expression),
    /// From integer
    FromInt(Expression),

    /* Regex */
    /// str.to_re
    ToRe(Expression),
    /// re.all
    ReAll,
    /// re.none
    ReNone,
    /// re.allchar
    ReAllChar,
    /// re.range
    ReRange(Expression, Expression),
    /// re.concat
    ReConcat(Vec<Expression>),
    /// re.union
    ReUnion(Vec<Expression>),
    /// re.inter
    ReInter(Vec<Expression>),
    /// re.star
    ReStar(Expression),
    /// re.plus
    RePlus(Expression),
    /// re.opt
    ReOpt(Expression),
    /// re.comp
    ReComp(Expression),
    /// re.diff
    ReDiff(Expression, Expression),
    /// re.pow
    RePow(Expression, usize),
    /// re.loop
    ReLoop(Expression, usize, usize),
}

impl AstNode for StrExpr {
    fn children(&self) -> Vec<&Expression> {
        match self {
            StrExpr::Constant(_) | StrExpr::Var(_) => vec![],
            StrExpr::Concat(es) => es.iter().collect(),
            StrExpr::Length(e) => vec![e],
            StrExpr::InRe(e, r) => vec![e, r],
            StrExpr::Substr(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::At(e, i) => vec![e, i],
            StrExpr::PrefixOf(e1, e2) => vec![e1, e2],
            StrExpr::SuffixOf(e1, e2) => vec![e1, e2],
            StrExpr::Contains(e1, e2) => vec![e1, e2],
            StrExpr::IndexOf(e1, e2, e3)
            | StrExpr::Replace(e1, e2, e3)
            | StrExpr::ReplaceAll(e1, e2, e3)
            | StrExpr::ReplaceRe(e1, e2, e3)
            | StrExpr::ReplaceReAll(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::ToInt(e) | StrExpr::FromInt(e) => vec![e],

            StrExpr::ToRe(rs)
            | StrExpr::ReStar(rs)
            | StrExpr::RePlus(rs)
            | StrExpr::ReOpt(rs)
            | StrExpr::ReComp(rs) => vec![rs],
            StrExpr::ReAll | StrExpr::ReNone | StrExpr::ReAllChar => vec![],
            StrExpr::ReRange(expression, expression1) => vec![expression, expression1],
            StrExpr::ReConcat(vec) | StrExpr::ReUnion(vec) | StrExpr::ReInter(vec) => {
                vec.iter().collect()
            }
            StrExpr::ReDiff(e, e1) => vec![e, e1],
            StrExpr::RePow(e, _) | StrExpr::ReLoop(e, _, _) => vec![e],
        }
    }

    // fn is_atomic(&self) -> bool {
    //     self.sort() == Sort::Bool
    // }

    fn sort(&self) -> Sort {
        match self {
            StrExpr::Var(_)
            | StrExpr::Constant(_)
            | StrExpr::Concat(_)
            | StrExpr::Substr(_, _, _)
            | StrExpr::At(_, _)
            | StrExpr::Replace(_, _, _)
            | StrExpr::ReplaceAll(_, _, _)
            | StrExpr::ReplaceRe(_, _, _)
            | StrExpr::ReplaceReAll(_, _, _)
            | StrExpr::FromInt(_) => Sort::String,
            StrExpr::Length(_) | StrExpr::IndexOf(_, _, _) | StrExpr::ToInt(_) => Sort::Int,
            StrExpr::InRe(_, _)
            | StrExpr::PrefixOf(_, _)
            | StrExpr::SuffixOf(_, _)
            | StrExpr::Contains(_, _) => Sort::Bool,
            StrExpr::ToRe(_)
            | StrExpr::ReAll
            | StrExpr::ReNone
            | StrExpr::ReAllChar
            | StrExpr::ReRange(_, _)
            | StrExpr::ReConcat(_)
            | StrExpr::ReUnion(_)
            | StrExpr::ReInter(_)
            | StrExpr::ReStar(_)
            | StrExpr::RePlus(_)
            | StrExpr::ReOpt(_)
            | StrExpr::ReComp(_)
            | StrExpr::ReDiff(_, _)
            | StrExpr::RePow(_, _)
            | StrExpr::ReLoop(_, _, _) => Sort::RegLan,
        }
    }
}

impl Display for StrExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StrExpr::Var(v) => write!(f, "{}", v),
            StrExpr::Constant(c) => {
                let converted = c.chars().map(convert_smtlib_char).collect::<String>();
                write!(f, "\"{}\"", converted)
            }
            StrExpr::Concat(rs) => {
                if rs.len() == 1 {
                    return write!(f, "{}", rs[0]);
                }
                write!(f, "(str.++")?;
                for r in rs {
                    write!(f, " {}", r)?;
                }
                write!(f, ")")
            }
            StrExpr::Length(t) => write!(f, "(str.len {})", t),
            StrExpr::Substr(t, l, u) => write!(f, "(str.substr {} {} {})", t, l, u),
            StrExpr::At(t, i) => write!(f, "(str.at {} {})", t, i),
            StrExpr::PrefixOf(l, r) => write!(f, "(str.prefixof {} {})", l, r),
            StrExpr::SuffixOf(l, r) => write!(f, "(str.suffixof {} {})", l, r),
            StrExpr::Contains(l, r) => write!(f, "(str.contains {} {})", l, r),
            StrExpr::IndexOf(l, r, i) => write!(f, "(str.indexof {} {} {})", l, r, i),
            StrExpr::Replace(l, r, s) => write!(f, "(str.replace {} {} {})", l, r, s),
            StrExpr::ReplaceAll(l, r, s) => write!(f, "(str.replace_all {} {} {})", l, r, s),
            StrExpr::ReplaceRe(l, r, s) => write!(f, "(str.replace_re {} {} {})", l, r, s),
            StrExpr::ReplaceReAll(l, r, s) => write!(f, "(str.replace_re_all {} {} {})", l, r, s),
            StrExpr::ToInt(s) => write!(f, "(str.to_int {})", s),
            StrExpr::FromInt(e) => write!(f, "(str.from_int {})", e),
            StrExpr::InRe(l, r) => write!(f, "(str.in_re {} {})", l, r),
            StrExpr::ToRe(r) => write!(f, "(str.to_re {})", r),
            StrExpr::ReAll => write!(f, "re.all"),
            StrExpr::ReNone => write!(f, "re.none"),
            StrExpr::ReAllChar => write!(f, "re.allchar"),
            StrExpr::ReRange(r, r1) => write!(f, "(re.range {} {})", r, r1),
            StrExpr::ReConcat(vec) => {
                if vec.len() == 1 {
                    return write!(f, "{}", vec[0]);
                }
                write!(f, "(re.concat")?;
                for r in vec {
                    write!(f, " {}", r)?;
                }
                write!(f, ")")
            }
            StrExpr::ReUnion(vec) => {
                if vec.len() == 1 {
                    return write!(f, "{}", vec[0]);
                }
                write!(f, "(re.union")?;
                for r in vec {
                    write!(f, " {}", r)?;
                }
                write!(f, ")")
            }
            StrExpr::ReInter(vec) => {
                if vec.len() == 1 {
                    return write!(f, "{}", vec[0]);
                }
                write!(f, "(re.inter")?;
                for r in vec {
                    write!(f, " {}", r)?;
                }
                write!(f, ")")
            }
            StrExpr::ReStar(r) => write!(f, "(re.* {})", r),
            StrExpr::RePlus(r) => write!(f, "(re.+ {})", r),
            StrExpr::ReOpt(r) => write!(f, "(re.opt {})", r),
            StrExpr::ReComp(r) => write!(f, "(re.comp {})", r),
            StrExpr::ReDiff(r, r1) => write!(f, "(re.diff {} {})", r, r1),
            StrExpr::ReLoop(r, l, u) => write!(f, "(_ re.loop {} {}) {})", l, u, r),
            StrExpr::RePow(r, e) => write!(f, "(_ re.pow {}) {}", e, r),
        }
    }
}
