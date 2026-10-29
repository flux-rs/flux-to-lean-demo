// A sort that nests one generic struct inside another (`Outer (Inner Int)`).
// The Lean encoding needs an `Inhabited (Inner Int)` instance for this to typecheck.
use flux_rs::attrs::*;

#[opaque]
#[refined_by(lo: T, hi: T)]
pub struct Inner<T> {
    _lo: T,
    _hi: T,
}

#[opaque]
#[refined_by(inner: T)]
pub struct Outer<T> {
    _inner: T,
}

#[trusted]
#[spec(fn(o: &Outer<Inner<usize>>[@x]) -> usize[x.inner.lo])]
pub fn lo(_o: &Outer<Inner<usize>>) -> usize {
    0
}

// The obligation must not be syntactically equal to a hypothesis, or flux
// simplifies the VC to `True` and the nested sort never reaches Lean.
#[proven_externally]
#[spec(fn(o: &Outer<Inner<usize>>[@x]) -> usize{v: v <= x.inner.hi}
    requires x.inner.lo < x.inner.hi)]
pub fn test(o: &Outer<Inner<usize>>) -> usize {
    lo(o) + 1
}
