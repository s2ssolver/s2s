use std::sync::atomic::AtomicU32;

static PVAR_COUNTER: AtomicU32 = AtomicU32::new(1);

pub type PVar = u32;
pub type PLit = i32;
pub type Clause = Vec<PLit>;
pub type Cnf = Vec<Clause>;

pub fn neg(var: PVar) -> PLit {
    -as_lit(var)
}
pub fn as_lit(var: PVar) -> PLit {
    var as i32
}
/// Returns a new unused propositional variable
pub fn pvar() -> PVar {
    let v = PVAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    if v > i32::MAX as u32 {
        panic!("Too many propositional variables")
    }
    v as PVar
}
