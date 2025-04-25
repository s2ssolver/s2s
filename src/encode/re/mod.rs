mod nfa;

pub use nfa::NFAEncoder;

use crate::{context::Context, ir::RegularConstraint};

pub fn build_inre_encoder(inre: &RegularConstraint, pol: bool, ctx: &mut Context) -> NFAEncoder {
    let v = inre.lhs().as_variable().expect("Not in canonical form");
    let re = inre.re();
    let nfa = ctx.get_nfa(re);
    NFAEncoder::new(v, nfa, pol)
}
