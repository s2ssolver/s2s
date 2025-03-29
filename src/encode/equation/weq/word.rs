use indexmap::IndexMap;
use rustsat::{clause, types::TernaryVal};
use rustsat_cadical::CaDiCaL;
use smt_str::SmtChar;

use crate::{
    alphabet::Alphabet,
    encode::{card::exactly_one, EncodingSink, LAMBDA},
    sat::{nlit, plit, pvar, PVar},
};
use rustsat::solvers::Solve;

/// Encodes the set of all words over a finite alphabet up to a given length.
pub struct WordEncoding {
    alphabet: Alphabet,
    length: usize,
    encoding: IndexMap<(usize, SmtChar), PVar>,
}

impl WordEncoding {
    pub fn new(alphabet: Alphabet) -> Self {
        Self {
            alphabet,
            length: 0,
            encoding: IndexMap::new(),
        }
    }

    /// Encodes the set of all words up to a given length.
    /// Must be called in increasing order of length.
    /// Panics if called with a length smaller than the current length.
    /// Is a no-op if called with the same length as the current length.
    pub fn encode(&mut self, length: usize, sink: &mut impl EncodingSink) {
        assert!(length >= self.length, "Length cannot shrink");

        let last_len = self.length;

        for pos in last_len..length {
            // This position needs to be filled with exactly-one letter from the alphabet
            let mut choices = Vec::with_capacity(self.alphabet.len());
            for symbol in self.alphabet.iter() {
                let choice = pvar();
                // choice <-> w[len] = symbol
                self.encoding.insert((pos, symbol), choice);
                choices.push(choice);
            }
            // add lambda
            let lambda_choice = pvar();
            self.encoding.insert((pos, LAMBDA), lambda_choice);
            choices.push(lambda_choice);
            // encode exactly-one
            let eo = exactly_one(&choices);
            sink.add_cnf(eo);

            // Symmetry breaking: If a position is lambda, then only lambda may follow
            if pos > 0 {
                let last_lambda = self.at(pos - 1, LAMBDA);
                sink.add_clause(clause![nlit(last_lambda), plit(lambda_choice)]);
            }
        }

        self.length = length;
    }

    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns the Boolean variable representing the presence of a symbol at a given position.
    /// The returned Boolean variable is true if and only if the word at the given position is the given symbol.
    /// Panics if the encoding for the given position and symbol does not exist.
    pub fn at(&self, len: usize, symbol: SmtChar) -> PVar {
        self.encoding
            .get(&(len, symbol))
            .copied()
            .unwrap_or_else(|| panic!("No encoding for w[{}] = {}", len, symbol))
    }

    #[allow(dead_code)]
    pub(super) fn print_solution_word(&self, solver: &mut CaDiCaL) {
        for len in 0..self.length {
            let mut found = false;
            let sol = solver.full_solution().unwrap();
            for symbol in self.alphabet.iter() {
                if sol.lit_value(plit(self.at(len, symbol))) == TernaryVal::True {
                    print!("{}", symbol);
                    found = true;
                    break;
                }
            }
            if found {
                continue;
            }
            if sol.lit_value(plit(self.at(len, LAMBDA))) == TernaryVal::True {
                print!("λ");
                continue;
            }
            panic!("No symbol at position {}", len);
        }
        println!();
    }
}
