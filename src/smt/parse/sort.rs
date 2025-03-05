use itertools::Itertools;
use smt2parser::visitors;

use crate::{node::Sort, smt::AstError};

use super::Symbol;

impl visitors::SortVisitor<Symbol> for super::ScriptBuilder<'_> {
    type T = Sort;

    type E = AstError;

    fn visit_simple_sort(
        &mut self,
        identifier: visitors::Identifier<Symbol>,
    ) -> Result<Self::T, Self::E> {
        match identifier {
            visitors::Identifier::Simple { symbol } => match symbol.as_str() {
                "Bool" => Ok(Sort::Bool),
                "Int" => Ok(Sort::Int),
                "String" => Ok(Sort::String),
                "RegLan" => Ok(Sort::RegLan),
                _ => Err(AstError::Unsupported(format!("Simple sort: {}", symbol))),
            },
            visitors::Identifier::Indexed { symbol, indices } => Err(AstError::Unsupported(
                format!("Indexed sort: {} {}", symbol, indices.iter().join(" ")),
            )),
        }
    }

    fn visit_parameterized_sort(
        &mut self,
        identifier: visitors::Identifier<Symbol>,
        parameters: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        Err(AstError::Unsupported(format!(
            "Parameterized sort: {} {}",
            identifier,
            parameters.iter().format(" ")
        )))
    }
}
