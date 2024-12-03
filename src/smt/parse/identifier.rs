use crate::{
    node::Sort,
    smt::{AstError, Identifier, Index, Symbol},
};
use num_traits::cast::ToPrimitive;
use smt2parser::visitors::{self};

impl<'a> visitors::QualIdentifierVisitor<smt2parser::concrete::Identifier<Symbol>, Sort>
    for super::ScriptBuilder<'a>
{
    type T = Identifier;

    type E = AstError;

    fn visit_simple_identifier(
        &mut self,
        identifier: smt2parser::concrete::Identifier<Symbol>,
    ) -> Result<Self::T, Self::E> {
        match identifier {
            visitors::Identifier::Simple { symbol } => Ok(Identifier::simple(symbol)),
            visitors::Identifier::Indexed { symbol, indices } => {
                let mut new_indices = Vec::with_capacity(indices.len());
                for idx in indices {
                    let converted = match idx {
                        visitors::Index::Numeral(n) => match n.to_usize().map(Index::Num) {
                            Some(i) => i,
                            None => return Err(AstError::NumeralOutOfBounds(n)),
                        },
                        visitors::Index::Symbol(s) => Index::Symbol(s),
                    };
                    new_indices.push(converted);
                }
                Ok(Identifier::indexed(symbol, new_indices))
            }
        }
    }

    fn visit_sorted_identifier(
        &mut self,
        _identifier: smt2parser::concrete::Identifier<Symbol>,
        _sort: Sort,
    ) -> Result<Self::T, Self::E> {
        Err(super::AstError::Unsupported(
            "Sorted identifier".to_string(),
        ))
    }
}
