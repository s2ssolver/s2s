mod nfa;

pub use nfa::NFAEncoder;

use crate::ast::{canonical::RegularConstraint, NodeManager};

pub fn build_inre_encoder(
    inre: &RegularConstraint,
    pol: bool,
    mngr: &mut NodeManager,
) -> NFAEncoder {
    let v = inre.lhs();
    let re = inre.re();
    let nfa = mngr.get_nfa(re);
    NFAEncoder::new(v, nfa, pol)
}
