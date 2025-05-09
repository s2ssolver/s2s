use std::{fmt::Display, rc::Rc};

use smt_str::{SmtChar, SmtString};

use crate::{
    ast::{Node, NodeKind, Sorted, Variable},
    context::Context,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Symbol {
    /// A constant character
    Const(SmtChar),
    /// A variable symbol
    Variable(Rc<Variable>),
    /// Something else
    Other(Node),
}

impl Symbol {
    pub fn is_const(&self) -> bool {
        matches!(self, Symbol::Const(_))
    }

    pub fn is_variable(&self) -> bool {
        matches!(self, Symbol::Variable(_))
    }

    pub fn is_other(&self) -> bool {
        matches!(self, Symbol::Other(_))
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Symbol::Const(ch) => write!(f, "{}", ch),
            Symbol::Variable(v) => write!(f, "{}", v),
            Symbol::Other(node) => write!(f, "{}", node),
        }
    }
}

/// Iterator over the symbols in a node that represents a string term.
pub struct PatternIterator<'a> {
    node: &'a Node,
    index: usize,
    sub_iter: Option<Box<PatternIterator<'a>>>,
}

impl<'a> PatternIterator<'a> {
    pub fn new(node: &'a Node) -> Self {
        PatternIterator {
            node,
            index: 0,
            sub_iter: None,
        }
    }

    pub fn peek(&self) -> Option<Symbol> {
        match self.node.kind() {
            NodeKind::String(s) => s.nth(self.index).map(Symbol::Const),
            NodeKind::Variable(v) if v.sort().is_string() => {
                // Return the variable symbol and move to the next child
                if self.index > 0 {
                    return None; // Stop if we've already returned the only symbol
                }
                Some(Symbol::Variable(v.clone()))
            }
            NodeKind::Concat => {
                if let Some(sub_iter) = &self.sub_iter {
                    if let Some(sym) = sub_iter.peek() {
                        return Some(sym);
                    }
                }
                // If the active sub-iterator is exhausted, try the next child, until a symbol is found
                // This is required to because we migth see concatenations of empty strings
                let mut n = self.index;
                while n < self.node.children().len() {
                    let nth = self.node.children().get(self.index)?;
                    // iterate over the children of the Concat node
                    let sub_iter = Box::new(PatternIterator::new(nth));
                    if let Some(sym) = sub_iter.peek() {
                        return Some(sym);
                    }
                    n += 1;
                }
                None
            }
            _ => Some(Symbol::Other(self.node.clone())),
        }
    }

    /// Creates a new node that represents a string term representing the remaining symbols in the iterator.
    /// If the iterator is fully exhausted, returns the node that represents the empty string.
    /// If the iterator encounter a non-string-symbol (i.e., not a constant string, string variable, or concatenation), returns `None`.
    pub fn to_node(mut self, ctx: &mut Context) -> Option<Node> {
        if self.index == 0 {
            // If the iterator has not been advanced, return the original node
            return Some(self.node.clone());
        }
        match self.node.kind() {
            NodeKind::String(s) => {
                // Process constant characters within the string
                let ch = s.drop(self.index);
                Some(ctx.ast().const_string(ch))
            }
            NodeKind::Variable(v) if v.sort().is_string() => {
                // Return the variable symbol and move to the next child
                if self.index > 0 {
                    Some(ctx.ast().empty_string())
                } else {
                    Some(ctx.ast().variable(v.clone()))
                }
            }
            NodeKind::Concat => {
                let mut children = Vec::new();
                // if the iterator has not been advanced, the original was already returned
                // otherwise, sub_iter is either Some or we already processed all children
                while let Some(sub_iter) = self.sub_iter {
                    let n = sub_iter.to_node(ctx)?;
                    children.push(n);

                    self.sub_iter = if self.index < self.node.children().len() {
                        Some(Box::new(PatternIterator::new(
                            &self.node.children()[self.index],
                        )))
                    } else {
                        None
                    };
                    self.index += 1;
                }
                Some(ctx.ast().concat(children))
            }
            _ => None,
        }
    }
}

impl Iterator for PatternIterator<'_> {
    type Item = Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        // Continue with any active sub-iterator first
        if let Some(ref mut sub_iter) = self.sub_iter {
            if let Some(sym) = sub_iter.next() {
                return Some(sym);
            } else {
                self.sub_iter = None; // Move on if sub-iterator is exhausted
            }
        }

        match self.node.kind() {
            NodeKind::String(s) => {
                // Process constant characters within the string
                if self.index < s.len() {
                    let ch = s.nth(self.index)?;
                    self.index += 1;
                    Some(Symbol::Const(ch))
                } else {
                    None
                }
            }
            NodeKind::Variable(v) if v.sort().is_string() => {
                // Return the variable symbol and move to the next child
                if self.index > 0 {
                    return None; // Stop if we've already returned the only symbol
                }
                self.index += 1;
                Some(Symbol::Variable(v.clone()))
            }
            NodeKind::Concat => {
                let nth = self.node.children().get(self.index)?;
                self.index += 1;
                // iterate over the children of the Concat node
                self.sub_iter = Some(Box::new(PatternIterator::new(nth)));
                self.next()
            }
            _ => Some(Symbol::Other(self.node.clone())),
        }
    }
}
/// If `node` is a string term, returns the longest constant prefix of the string.
/// If the `node` is a concatenation of strings and variables, it accumulates
/// the constant prefix until encountering a variable or non-string term.
/// Otherwise, returns `None`.
pub fn const_prefix(node: &Node) -> Option<SmtString> {
    match node.kind() {
        NodeKind::String(s) => Some(s.clone()), // Directly a constant string
        NodeKind::Variable(v) if v.sort().is_string() => Some(SmtString::empty()), // Empty prefix for a variable
        NodeKind::Concat => {
            let mut prefix = SmtString::empty();
            // Accumulate the prefix from each child until a variable or non-string is encountered
            for child in node.children() {
                match child.kind() {
                    NodeKind::String(s) => prefix.append(s),
                    NodeKind::Variable(v) if v.sort().is_string() => break, // Stop on first variable
                    NodeKind::Concat => {
                        // Recursively accumulate the prefix from nested concatenations
                        let nested_prefix = const_prefix(child)?;
                        prefix.append(&nested_prefix);
                    }
                    _ => return Some(prefix), // Stop on first non-string/non-variable term
                }
            }
            Some(prefix)
        }
        _ => None, // Not a string term
    }
}

/// If `node` is a string term, returns the longest constant suffix of the string.
/// If the `node` is a concatenation of strings and variables, it accumulates
/// the constant suffix until encountering a variable or non-string term.
/// Otherwise, returns `None`.
pub fn const_suffix(node: &Node) -> Option<SmtString> {
    match node.kind() {
        NodeKind::String(s) => Some(s.clone()), // Directly a constant string
        NodeKind::Variable(v) if v.sort().is_string() => Some(SmtString::empty()), // Empty suffix for a variable
        NodeKind::Concat => {
            let mut suffix_parts = Vec::new();

            // Traverse the children in reverse to accumulate the suffix
            for child in node.children().iter().rev() {
                match child.kind() {
                    NodeKind::String(s) => suffix_parts.push(s.clone()),
                    NodeKind::Variable(v) if v.sort().is_string() => break, // Stop at first variable
                    NodeKind::Concat => {
                        // Recursively accumulate the suffix from nested concatenations
                        if let Some(nested_suffix) = const_suffix(child) {
                            suffix_parts.push(nested_suffix);
                        } else {
                            break; // Stop if nested concat has non-constant part
                        }
                    }
                    _ => return None, // Stop on first non-string/non-variable term
                }
            }

            // Combine the parts in reverse order to form the final suffix
            Some(suffix_parts.into_iter().rev().collect())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Sort;

    use super::*;

    #[test]
    fn test_const_prefix_with_constant_string() {
        let mut ctx = Context::default();

        // Test with a simple constant string
        let node = ctx.ast().const_str("foo");
        assert_eq!(const_prefix(&node), Some("foo".into()));
    }

    #[test]
    fn test_const_prefix_with_concat_of_strings() {
        let mut ctx = Context::default();

        // Concatenation of two constant strings
        let string_foo = ctx.ast().const_str("foo");
        let string_bar = ctx.ast().const_str("bar");
        let node = ctx.ast().concat(vec![string_foo, string_bar]);

        assert_eq!(const_prefix(&node), Some("foobar".into()));
    }

    #[test]
    fn test_const_prefix_with_concat_with_variable() {
        let mut ctx = Context::default();

        // Concatenation of a constant string and a variable
        let string_foo = ctx.ast().const_str("foo");
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x);
        let node = ctx.ast().concat(vec![string_foo, var_x.clone()]);

        // Prefix should stop at variable
        assert_eq!(const_prefix(&node), Some("foo".into()));
    }

    #[test]
    fn test_const_prefix_with_nested_concat() {
        let mut ctx = Context::default();

        // Nested concatenation with strings and a variable
        let string_abc = ctx.ast().const_str("abc");
        let string_def = ctx.ast().const_str("def");
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x);

        // Create the inner concatenation "def" + var_x
        let inner_concat = ctx.ast().concat(vec![string_def, var_x.clone()]);
        // Create the outer concatenation "abc" + inner_concat
        let node = ctx.ast().concat(vec![string_abc, inner_concat]);

        // Expect "abcdef" as the longest prefix, stopping at the variable
        assert_eq!(const_prefix(&node), Some("abcdef".into()));
    }

    #[test]
    fn test_const_prefix_with_non_string_term() {
        let mut ctx = Context::default();

        // Test with a non-string node
        let node = ctx.ast().const_int(42);
        assert_eq!(const_prefix(&node), None);
    }

    #[test]
    fn test_const_prefix_empty_concat() {
        let mut ctx = Context::default();

        // Empty concatenation
        let node = ctx.ast().concat(vec![]);
        assert_eq!(const_prefix(&node), Some("".into())); // Empty concat should return an empty prefix
    }

    #[test]
    fn test_const_suffix_with_constant_string() {
        let mut ctx = Context::default();

        // Test with a simple constant string
        let node = ctx.ast().const_str("foo");
        assert_eq!(const_suffix(&node), Some("foo".into()));
    }

    #[test]
    fn test_const_suffix_with_concat_of_strings() {
        let mut ctx = Context::default();

        // Concatenation of two constant strings
        let string_foo = ctx.ast().const_str("foo");
        let string_bar = ctx.ast().const_str("bar");
        let node = ctx.ast().concat(vec![string_foo, string_bar]);

        assert_eq!(const_suffix(&node), Some("foobar".into()));
    }

    #[test]
    fn test_const_suffix_with_concat_with_variable() {
        let mut ctx = Context::default();

        // Concatenation of a constant string and a variable
        let string_foo = ctx.ast().const_str("foo");
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x);
        let node = ctx.ast().concat(vec![var_x.clone(), string_foo]);

        // Suffix should stop at variable
        assert_eq!(const_suffix(&node), Some("foo".into()));
    }

    #[test]
    fn test_const_suffix_with_nested_concat() {
        let mut ctx = Context::default();

        // Nested concatenation with strings and a variable
        let string_abc = ctx.ast().const_str("abc");
        let string_def = ctx.ast().const_str("def");
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x);

        // Create the inner concatenation var_x + "abc"
        let inner_concat = ctx.ast().concat(vec![var_x.clone(), string_abc]);
        // Create the outer concatenation inner_concat + "def"
        let node = ctx.ast().concat(vec![inner_concat, string_def]);

        // Expect "defabc" as the longest suffix, stopping at the variable
        assert_eq!(const_suffix(&node), Some("abcdef".into()));
    }

    #[test]
    fn test_const_suffix_with_non_string_term() {
        let mut ctx = Context::default();

        // Test with a non-string node
        let node = ctx.ast().const_int(42);
        assert_eq!(const_suffix(&node), None);
    }

    #[test]
    fn test_const_suffix_empty_concat() {
        let mut ctx = Context::default();

        // Empty concatenation
        let node = ctx.ast().concat(vec![]);
        assert_eq!(const_suffix(&node), Some("".into())); // Empty concat should return an empty suffix
    }

    #[test]
    fn test_symbol_iterator_with_simple_string() {
        let mut ctx = Context::default();
        let node = ctx.ast().const_str("abcde");
        let mut iter = PatternIterator::new(&node);

        assert_eq!(iter.next(), Some(Symbol::Const('a'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('b'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('c'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('d'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('e'.into())));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_symbol_iterator_with_variable() {
        let mut ctx = Context::default();

        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x.clone());
        let mut iter = PatternIterator::new(&var_x);

        assert_eq!(iter.next(), Some(Symbol::Variable(x.clone())));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_symbol_iterator_with_concat_of_string_and_variable() {
        let mut ctx = Context::default();

        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x.clone());
        let string_hello = ctx.ast().const_str("abcde");
        let node = ctx.ast().concat(vec![string_hello, var_x.clone()]);
        let mut iter = PatternIterator::new(&node);

        assert_eq!(iter.next(), Some(Symbol::Const('a'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('b'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('c'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('d'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('e'.into())));
        assert_eq!(iter.next(), Some(Symbol::Variable(x.clone())));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_symbol_iterator_with_nested_concat() {
        let mut ctx = Context::default();

        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x.clone());
        let string_foo = ctx.ast().const_str("foo");
        let string_bar = ctx.ast().const_str("bar");

        // Create nested concatenation: ("foo" + ("bar" + var_x))
        let inner_concat = ctx.ast().concat(vec![string_bar, var_x.clone()]);
        let node = ctx.ast().concat(vec![string_foo, inner_concat]);
        let mut iter = PatternIterator::new(&node);

        assert_eq!(iter.next(), Some(Symbol::Const('f'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('o'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('o'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('b'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('a'.into())));
        assert_eq!(iter.next(), Some(Symbol::Const('r'.into())));
        assert_eq!(iter.next(), Some(Symbol::Variable(x.clone())));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn to_node_constant_string() {
        let mut ctx = Context::default();
        let node = ctx.ast().const_str("abcde");

        let iter = PatternIterator::new(&node);
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, node);

        let mut iter = PatternIterator::new(&node);
        iter.next();
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, ctx.ast().const_str("bcde"));

        let mut iter = PatternIterator::new(&node);
        iter.next();
        iter.next();
        iter.next();
        iter.next();
        iter.next();
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, ctx.ast().empty_string());
    }

    #[test]
    fn to_node_single_var() {
        let mut ctx = Context::default();
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x.clone());

        let iter = PatternIterator::new(&var_x);
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, var_x);

        let mut iter = PatternIterator::new(&var_x);
        iter.next();
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, ctx.ast().empty_string());
    }

    #[test]
    fn to_node_concat_nested() {
        let mut ctx = Context::default();
        let x = ctx.temp_var(Sort::String);
        let var_x = ctx.ast().variable(x.clone());
        let string_foo = ctx.ast().const_str("foo");
        let string_bar = ctx.ast().const_str("bar");

        // Create nested concatenation: ("foo" + ("bar" + var_x))
        let inner_concat = ctx.ast().concat(vec![string_bar.clone(), var_x.clone()]);
        let node = ctx.ast().concat(vec![string_foo, inner_concat.clone()]);

        let iter = PatternIterator::new(&node);
        let new_node = iter.to_node(&mut ctx).unwrap();
        assert_eq!(new_node, node);

        let mut iter = PatternIterator::new(&node);
        iter.next();
        let new_node = iter.to_node(&mut ctx).unwrap();
        let string_oo = ctx.ast().const_str("oo");
        let expected = ctx.ast().concat(vec![string_oo, inner_concat]);
        assert_eq!(
            new_node, expected,
            "Expected: {}, Actual: {}",
            expected, new_node
        );

        let mut iter = PatternIterator::new(&node);
        for _ in 0..7 {
            iter.next();
        }
        let new_node = iter.to_node(&mut ctx).unwrap();

        let expected = ctx.ast().empty_string();
        assert_eq!(new_node, expected,);
    }
}
