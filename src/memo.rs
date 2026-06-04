use std::collections::HashMap;

use flux_rs::attrs::*;

// -------------------------------------------------------------------------
// An API for a `Memo` table with a *generic* key-value refinement
// -------------------------------------------------------------------------

#[opaque]
#[flux_rs::refined_by(hdl kv: (int, T) -> bool)]
pub struct Memo<T> {
    inner: HashMap<usize, T>,
}

#[trusted]
impl<T> Memo<T> {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    #[spec(fn(&Self[@kv], key: usize) -> Option<&T{v: kv(key, v)}>)]
    pub fn get(&self, key: usize) -> Option<&T> {
        self.inner.get(&key)
    }

    #[spec(fn(me: &mut Self[@kv], key: usize, value: T{kv(key, value)}))]
    pub fn set(&mut self, key: usize, value: T) {
        self.inner.insert(key, value);
    }
}

macro_rules! memo {
    ($T:ty, $($pred:tt)*) => {
        {
            #[trusted]
            #[spec(fn() -> Memo<$T>[$($pred)*])]
            fn new_memo() -> Memo<$T> {
                Memo::new()
            }
            new_memo()
        }
    };
}

// -------------------------------------------------------------------------
// Example usage of the memoization table
// -------------------------------------------------------------------------

#[proven_externally(proof)]
#[spec(fn(n: usize, m: &mut Memo<usize>[|k, v| v == spec_fib(k)]) -> usize[spec_fib(n)])]
pub fn fib_memo(n: usize, m: &mut Memo<usize>) -> usize {
    let res = if n <= 1 {
        1
    } else if let Some(v) = m.get(n) {
        *v
    } else {
        let v = fib_memo(n - 1, m) + fib_memo(n - 2, m);
        m.set(n, v);
        v
    };
    res
}

pub fn test_memo() {
    let mut m = memo! {usize, |k, v| k < v};
    m.set(1, 2);
    m.set(11, 22);

    if let Some(v) = m.get(11) {
        flux_rs::assert(11 < *v);
    }
    if let Some(v) = m.get(1) {
        flux_rs::assert(1 < *v);
    }
}
