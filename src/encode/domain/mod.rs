//! Encoding of the domains of all variables.

mod bool;
mod int;
mod string;

use std::rc::Rc;

use bool::{BoolDomain, BoolEncoder};

pub use int::IntDomain;
use int::IntegerEncoder;
use rustsat_cadical::CaDiCaL;
pub use string::StringDomain;
use string::StringDomainEncoder;

use crate::{alphabet::Alphabet, ast::VarSubstitution, context::Context, domain::Domain};

use super::EncodingSink;

/// Propositional encoding of the domains of all variables.
#[derive(Clone, Debug)]
pub struct DomainEncoding {
    /// The encoding of the substitutions
    string: StringDomain,
    /// The encoding of the integer domains
    int: IntDomain,
    /// The encooding of Boolean variables
    bool: BoolDomain,

    /// The alphabet used for the substitutions
    alphabet: Rc<Alphabet>,

    /// The bounds of the integer variables
    pub(super) dom: Domain,
}

impl DomainEncoding {
    pub fn new(alphabet: Rc<Alphabet>, bounds: Domain) -> Self {
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

    pub fn get_model(&self, solver: &CaDiCaL, ctx: &mut Context) -> VarSubstitution {
        let mut model = self.string.get_model(solver, &self.dom, ctx);
        model.extend(&self.int.get_model(solver, ctx));
        model.extend(&self.bool.get_model(solver, ctx));
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
    pub fn new(alphabet: Rc<Alphabet>) -> Self {
        Self {
            strings: StringDomainEncoder::new(alphabet),
            integers: IntegerEncoder::new(),
            bool: BoolEncoder::default(),
            encoding: None,
        }
    }

    /// Encodes the domain of all variables for which bounds are given.
    pub fn encode(&mut self, dom: &Domain, sink: &mut impl EncodingSink) {
        let mut encoding = self.encoding.take().unwrap_or(DomainEncoding::new(
            Rc::new(self.strings.alphabet().clone()),
            dom.clone(),
        ));

        // Bool encoding does not depend on the bounds and does not return a CNF.
        self.bool.encode(&mut encoding, dom);

        self.strings.encode(dom, &mut encoding, sink);

        self.integers.encode(dom, &mut encoding, sink);
        encoding.dom = dom.clone();
        self.encoding = Some(encoding);
    }

    pub fn encoding(&self) -> &DomainEncoding {
        self.encoding.as_ref().unwrap()
    }
}

// TODO: Encode lengths here.
