//! Encoding of the domains of all variables.

mod bool;
mod int;
mod string;

use bool::{BoolDomain, BoolEncoder};

pub use int::IntDomain;
use int::IntegerEncoder;
pub use string::StringDomain;
use string::StringDomainEncoder;

use crate::{
    alphabet::Alphabet, domain::Domain, encode::EncodingResult, node::canonical::Assignment,
};

#[derive(Clone, Debug)]
pub struct DomainEncoding {
    /// The encoding of the substitutions
    string: StringDomain,
    /// The encoding of the integer domains
    int: IntDomain,
    /// The encooding of Boolean variables
    bool: BoolDomain,

    /// The alphabet used for the substitutions
    alphabet: Alphabet,

    /// The bounds of the integer variables
    pub(super) dom: Domain,
}

/// Propositional encoding of the domains of all variables.

impl DomainEncoding {
    pub fn new(alphabet: Alphabet, bounds: Domain) -> Self {
        Self {
            string: StringDomain::new(),
            int: IntDomain::default(),
            bool: BoolDomain::default(),
            alphabet,
            dom: bounds,
        }
    }

    pub fn string(&self) -> &StringDomain {
        &self.string
    }

    pub fn int(&self) -> &IntDomain {
        &self.int
    }

    pub fn bool(&self) -> &BoolDomain {
        &self.bool
    }

    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    pub fn get_model(&self, solver: &cadical::Solver) -> Assignment {
        let mut model = self.string.get_model(solver, &self.dom);
        let overwrite = model.extend(&self.int.get_model(solver));
        assert!(overwrite == 0);
        let overwrite = model.extend(&self.bool.get_model(solver));
        assert!(overwrite == 0);
        model
    }
}

/// Encoder for the domains of all variables.
pub struct DomainEncoder {
    /// The encoder for string variables
    strings: StringDomainEncoder,
    /// The encoder for integer variables
    integers: IntegerEncoder,

    bool: BoolEncoder,

    encoding: Option<DomainEncoding>,
}

impl DomainEncoder {
    pub fn new(alphabet: Alphabet) -> Self {
        Self {
            strings: StringDomainEncoder::new(alphabet),
            integers: IntegerEncoder::new(),
            bool: BoolEncoder::default(),
            encoding: None,
        }
    }

    /// Encodes the domain of all variables for which bounds are given.
    pub fn encode(&mut self, dom: &Domain) -> EncodingResult {
        let mut encoding = self.encoding.take().unwrap_or(DomainEncoding::new(
            self.strings.alphabet().clone(),
            dom.clone(),
        ));

        // Bool encoding does not depend on the bounds and does not return a CNF.
        self.bool.encode(&mut encoding, dom);

        let mut res = self.strings.encode(dom, &mut encoding);

        res.extend(self.integers.encode(dom, &mut encoding));
        encoding.dom = dom.clone();
        self.encoding = Some(encoding);
        res
    }

    pub fn encoding(&self) -> &DomainEncoding {
        self.encoding.as_ref().unwrap()
    }
}

// TODO: Encode lengths here.
