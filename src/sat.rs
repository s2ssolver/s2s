use std::sync::atomic::AtomicU32;

static PVarCounter: AtomicU32 = AtomicU32::new(1);

pub type PVar = u32;
pub type PLit = i64;
pub type Clause = Vec<PLit>;
pub type Cnf = Vec<Clause>;

pub fn neg(var: PVar) -> PLit {
    -asLit(var)
}
pub fn asLit(var: PVar) -> PLit {
    var as i64
}
/// Returns a new unused propositional variable
pub fn pvar() -> PVar {
    PVarCounter.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
}
