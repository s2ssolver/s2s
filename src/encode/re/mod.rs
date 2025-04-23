mod nfa;

pub use nfa::NFAEncoder;

use crate::{ast::canonical::RegularConstraint, context::Context};

pub fn build_inre_encoder(inre: &RegularConstraint, pol: bool, ctx: &mut Context) -> NFAEncoder {
    let v = inre.lhs();
    let re = inre.re();
    let nfa = ctx.get_nfa(re);
    NFAEncoder::new(v, nfa, pol)
}
