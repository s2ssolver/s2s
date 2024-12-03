use indexmap::IndexMap;

use crate::{
    alphabet::Alphabet,
    encode::{card::exactly_one, EncodingResult, LAMBDA},
    sat::{nlit, plit, pvar, PVar},
};

/// Encodes the set of all words over a finite alphabet up to a given length.
pub struct WordEncoding {
    alphabet: Alphabet,
    length: usize,
    encoding: IndexMap<(usize, char), PVar>,
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
    pub fn encode(&mut self, length: usize) -> EncodingResult {
        assert!(length >= self.length, "Length cannot shrink");
        let mut clauses = Vec::new();
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
            clauses.extend(eo);

            // Symmetry breaking: If a position is lambda, then only lambda may follow
            if pos > 0 {
                let last_lambda = self.at(pos - 1, LAMBDA);
                clauses.push(vec![nlit(last_lambda), plit(lambda_choice)]);
            }
        }

        self.length = length;
        EncodingResult::cnf(clauses)
    }

    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns the Boolean variable representing the presence of a symbol at a given position.
    /// The returned Boolean variable is true if and only if the word at the given position is the given symbol.
    /// Panics if the encoding for the given position and symbol does not exist.
    pub fn at(&self, len: usize, symbol: char) -> PVar {
        self.encoding
            .get(&(len, symbol))
            .copied()
            .unwrap_or_else(|| panic!("No encoding for w[{}] = {}", len, symbol))
    }

    #[allow(dead_code)]
    pub(super) fn print_solution_word(&self, solver: &cadical::Solver) {
        for len in 0..self.length {
            let mut found = false;
            for symbol in self.alphabet.iter() {
                if solver.value(plit(self.at(len, symbol))).unwrap_or(false) {
                    print!("{}", symbol);
                    found = true;
                    break;
                }
            }
            if found {
                continue;
            }
            if solver.value(plit(self.at(len, LAMBDA))).unwrap_or(false) {
                print!("λ");
                continue;
            }
            panic!("No symbol at position {}", len);
        }
        println!();
    }
}
