use std::{
    fmt::Display,
    hash::{Hash, Hasher},
    rc::Rc,
};

use itertools::Itertools;
use regulaer::re::Regex;

use crate::repr::{ast::convert_smtlib_char, Sort, Sorted, Variable};

/// The SMT-LIB core expressions
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum CoreExpr {
    /// A boolean constant
    Bool(bool),
    /// A boolean variable
    Var(Rc<Variable>),
    /// Boolean Negation
    Not(Rc<Expression>),
    /// Boolean Conjunction
    And(Vec<Rc<Expression>>),
    /// Boolean Disjunction
    Or(Vec<Rc<Expression>>),
    /// Boolean Equivalence
    Equal(Rc<Expression>, Rc<Expression>),
    /// Boolean Implication
    Imp(Rc<Expression>, Rc<Expression>),
    /// If-then-else
    Ite(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// Distinct
    Distinct(Vec<Rc<Expression>>),
}

impl CoreExpr {
    pub fn children(&self) -> Vec<&Rc<Expression>> {
        match self {
            CoreExpr::Bool(_) | CoreExpr::Var(_) => vec![],
            CoreExpr::Not(e) => vec![e],
            CoreExpr::And(es) => es.iter().collect(),
            CoreExpr::Or(es) => es.iter().collect(),
            CoreExpr::Equal(e1, e2) => vec![e1, e2],
            CoreExpr::Imp(e1, e2) => vec![e1, e2],
            CoreExpr::Ite(i, t, e) => vec![i, t, e],
            CoreExpr::Distinct(es) => es.iter().collect(),
        }
    }
}

impl Sorted for CoreExpr {
    fn sort(&self) -> Sort {
        match self {
            CoreExpr::Bool(_) => Sort::Bool,
            CoreExpr::Var(v) => v.sort(),
            CoreExpr::Not(_)
            | CoreExpr::And(_)
            | CoreExpr::Imp(_, _)
            | CoreExpr::Or(_)
            | CoreExpr::Distinct(_) => Sort::Bool,
            CoreExpr::Equal(l, r) => {
                let l_sort = l.sort();
                let r_sort = r.sort();
                assert!(
                    l_sort == r_sort,
                    "Sort mismatch for {}: {} != {}",
                    self,
                    l_sort,
                    r_sort
                );
                l_sort
            }
            CoreExpr::Ite(_, t, e) => {
                let t_sort = t.sort();
                let e_sort = e.sort();
                assert!(
                    t_sort == e_sort,
                    "Sort mismatch for {}: {} != {}",
                    self,
                    t_sort,
                    e_sort
                );
                t_sort
            }
        }
    }
}

impl Display for CoreExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoreExpr::Bool(b) => write!(f, "{}", b),
            CoreExpr::Var(v) => write!(f, "{}", v),
            CoreExpr::Not(e) => write!(f, "(not {})", e),
            CoreExpr::And(es) => {
                write!(f, "(and")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }

            CoreExpr::Or(es) => {
                write!(f, "(or")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            CoreExpr::Equal(e1, e2) => write!(f, "(= {} {})", e1, e2),
            CoreExpr::Imp(e1, e2) => write!(f, "(=> {} {})", e1, e2),
            CoreExpr::Ite(i, t, e) => write!(f, "(ite {} {} {})", i, t, e),
            CoreExpr::Distinct(es) => {
                write!(f, "(distinct")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// The SMT-LIB string expressions.
/// Note that these comprise the operations defined in the SMT-LIB theory of strings.
/// Not all expression are necessarily of sort String.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum StrExpr {
    /// A string constant
    Constant(String),

    /// A string variable
    Var(Rc<Variable>),

    /// A regular expression
    Regex(Regex),
    /// Concatenation
    Concat(Vec<Rc<Expression>>),
    /// Length
    Length(Rc<Expression>),
    InRe(Rc<Expression>, Rc<Expression>),
    /// Substring
    Substr(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// String at
    At(Rc<Expression>, Rc<Expression>),
    /// Prefix
    PrefixOf(Rc<Expression>, Rc<Expression>),
    /// Suffix
    SuffixOf(Rc<Expression>, Rc<Expression>),
    /// Contains
    Contains(Rc<Expression>, Rc<Expression>),
    /// Index of
    IndexOf(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// Replace
    Replace(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// Replace all
    ReplaceAll(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// Replace re
    ReplaceRe(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// Replace re all
    ReplaceReAll(Rc<Expression>, Rc<Expression>, Rc<Expression>),
    /// To integer
    ToInt(Rc<Expression>),
    /// From integer
    FromInt(Rc<Expression>),
}

impl StrExpr {
    pub fn children(&self) -> Vec<&Rc<Expression>> {
        match self {
            StrExpr::Constant(_) => vec![],
            StrExpr::Var(_) => vec![],
            StrExpr::Concat(es) => es.iter().collect(),
            StrExpr::Length(e) => vec![e],
            StrExpr::InRe(e, r) => vec![e, r],
            StrExpr::Substr(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::At(e, i) => vec![e, i],
            StrExpr::PrefixOf(e1, e2) => vec![e1, e2],
            StrExpr::SuffixOf(e1, e2) => vec![e1, e2],
            StrExpr::Contains(e1, e2) => vec![e1, e2],
            StrExpr::IndexOf(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::Replace(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::ReplaceAll(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::ReplaceRe(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::ReplaceReAll(e1, e2, e3) => vec![e1, e2, e3],
            StrExpr::ToInt(e) => vec![e],
            StrExpr::FromInt(e) => vec![e],
            StrExpr::Regex(_) => vec![],
        }
    }
}
impl Sorted for StrExpr {
    fn sort(&self) -> Sort {
        match self {
            StrExpr::Regex(_) => Sort::RegLang,
            StrExpr::Var(v) => {
                debug_assert!(v.sort() == Sort::String);
                Sort::String
            }
            StrExpr::Constant(_)
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
            StrExpr::Regex(r) => write!(f, "{}", regulaer::parse::to_smt(r)),
        }
    }
}

/// The SMT-LIB integer expressions.
/// Note that these comprise the operations defined in the SMT-LIB theory of integers (QF_*IA).
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum IntExpr {
    Constant(isize),
    Var(Rc<Variable>),
    Add(Vec<Rc<Expression>>),
    Sub(Rc<Expression>, Rc<Expression>),
    Mul(Vec<Rc<Expression>>),
    Div(Rc<Expression>, Rc<Expression>),
    Mod(Rc<Expression>, Rc<Expression>),
    Neg(Rc<Expression>),
    Abs(Rc<Expression>),
    Le(Rc<Expression>, Rc<Expression>),
    Lt(Rc<Expression>, Rc<Expression>),
    Ge(Rc<Expression>, Rc<Expression>),
    Gt(Rc<Expression>, Rc<Expression>),
}
impl IntExpr {
    pub fn children(&self) -> Vec<&Rc<Expression>> {
        match self {
            IntExpr::Constant(_) => vec![],
            IntExpr::Var(_) => vec![],
            IntExpr::Add(es) => es.iter().collect(),
            IntExpr::Sub(e1, e2) => vec![e1, e2],
            IntExpr::Mul(es) => es.iter().collect(),
            IntExpr::Div(e1, e2) => vec![e1, e2],
            IntExpr::Mod(e1, e2) => vec![e1, e2],
            IntExpr::Neg(e) => vec![e],
            IntExpr::Abs(e) => vec![e],
            IntExpr::Le(e1, e2) => vec![e1, e2],
            IntExpr::Lt(e1, e2) => vec![e1, e2],
            IntExpr::Ge(e1, e2) => vec![e1, e2],
            IntExpr::Gt(e1, e2) => vec![e1, e2],
        }
    }
}

impl Sorted for IntExpr {
    fn sort(&self) -> Sort {
        match self {
            IntExpr::Constant(_) => Sort::Int,
            IntExpr::Var(v) => {
                debug_assert!(v.sort() == Sort::Int);
                Sort::Int
            }
            IntExpr::Add(_)
            | IntExpr::Sub(_, _)
            | IntExpr::Mul(_)
            | IntExpr::Div(_, _)
            | IntExpr::Mod(_, _)
            | IntExpr::Neg(_)
            | IntExpr::Abs(_) => Sort::Int,
            IntExpr::Le(_, _) | IntExpr::Lt(_, _) | IntExpr::Ge(_, _) | IntExpr::Gt(_, _) => {
                Sort::Bool
            }
        }
    }
}

impl Display for IntExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntExpr::Constant(c) => write!(f, "{}", c),
            IntExpr::Var(v) => write!(f, "{}", v),
            IntExpr::Add(es) => {
                write!(f, "(+")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            IntExpr::Sub(e1, e2) => write!(f, "(- {} {})", e1, e2),
            IntExpr::Mul(es) => {
                write!(f, "(*")?;
                for e in es {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
            IntExpr::Div(e1, e2) => write!(f, "(div {} {})", e1, e2),
            IntExpr::Mod(e1, e2) => write!(f, "(mod {} {})", e1, e2),
            IntExpr::Neg(e) => write!(f, "(- {})", e),
            IntExpr::Abs(e) => write!(f, "(abs {})", e),
            IntExpr::Le(e1, e2) => write!(f, "(<= {} {})", e1, e2),
            IntExpr::Lt(e1, e2) => write!(f, "(< {} {})", e1, e2),
            IntExpr::Ge(e1, e2) => write!(f, "(>= {} {})", e1, e2),
            IntExpr::Gt(e1, e2) => write!(f, "(> {} {})", e1, e2),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ExprType {
    /// A Core, i.e. Boolean, expression
    Core(CoreExpr),
    /// A String Expression
    String(StrExpr),
    /// An Integer Expression
    Int(IntExpr),
}

impl Into<ExprType> for CoreExpr {
    fn into(self) -> ExprType {
        ExprType::Core(self)
    }
}

impl Into<ExprType> for StrExpr {
    fn into(self) -> ExprType {
        ExprType::String(self)
    }
}

impl Into<ExprType> for IntExpr {
    fn into(self) -> ExprType {
        ExprType::Int(self)
    }
}

impl ExprType {
    pub fn children(&self) -> Vec<&Rc<Expression>> {
        match self {
            ExprType::Core(c) => c.children(),
            ExprType::String(s) => s.children(),
            ExprType::Int(i) => i.children(),
        }
    }

    /// Returns true if the expression is an atomic formula.
    /// A formula is atomic if it is
    /// - an equality of two expressions (excluding Boolean equivalences)
    /// - a Boolean variable
    /// - a predicate symbol, i.e., an expression of sort Bool
    pub fn is_atomic(&self) -> bool {
        match self {
            // Equalities that are not Boolean equivalences are atoms
            ExprType::Core(CoreExpr::Equal(l, r)) => l.sort() == r.sort() && l.sort() != Sort::Bool,
            ExprType::Core(CoreExpr::Var(v)) => v.sort() == Sort::Bool,
            // Predicate symbols, i.e., expression that are of sort Bool are atoms
            ExprType::String(s) => s.sort() == Sort::Bool,
            ExprType::Int(s) => s.sort() == Sort::Bool,
            _ => false,
        }
    }

    /// Returns true iff the expression is a variable.
    pub fn is_variable(&self) -> bool {
        match self {
            ExprType::Core(CoreExpr::Var(_)) => true,
            _ => false,
        }
    }
}

impl Display for ExprType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprType::Core(c) => write!(f, "{}", c),
            ExprType::String(s) => write!(f, "{}", s),
            ExprType::Int(i) => write!(f, "{}", i),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Expression {
    id: usize,
    expr: ExprType,
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Expression {}

impl Expression {
    pub(crate) fn new(id: usize, expr: ExprType) -> Self {
        Self { id, expr }
    }

    pub fn get_type(&self) -> &ExprType {
        &self.expr
    }

    pub fn args(&self) -> Vec<&Rc<Expression>> {
        self.expr.children()
    }

    pub fn id(&self) -> usize {
        self.id
    }

    pub fn subexpressions(&self) -> SubExpressionIterator {
        SubExpressionIterator {
            stack: vec![Rc::new(self.clone())],
        }
    }

    pub fn is_const(&self) -> bool {
        todo!()
    }
}

impl Sorted for Expression {
    fn sort(&self) -> Sort {
        match self.get_type() {
            ExprType::Core(e) => e.sort(),
            ExprType::String(e) => e.sort(),
            ExprType::Int(e) => e.sort(),
        }
    }
}

impl Hash for Expression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expr)
    }
}

pub struct SubExpressionIterator {
    stack: Vec<Rc<Expression>>,
}
impl Iterator for SubExpressionIterator {
    type Item = Rc<Expression>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(expr) = self.stack.pop() {
            let children: Vec<Rc<Expression>> =
                expr.expr.children().into_iter().cloned().collect_vec();
            self.stack.extend(children);
            Some(expr)
        } else {
            None
        }
    }
}
