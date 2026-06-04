use flux_rs::assert;
use flux_rs::attrs::*;

defs! {
    opaque sort Arr<T>;
    fn arr_set<T>(a: Arr<T>, pos: int, v: T) -> Arr<T>;
    fn arr_get<T>(a: Arr<T>, pos: int) -> T;
    fn arr_eq_between<T>(a1: Arr<T>, a2: Arr<T>, l: int, r: int) -> bool;
}

#[opaque]
#[refined_by(elems: Arr<T>, len: int)]
#[invariant(len >= 0)]
pub struct AVec<T> {
    inner: Vec<T>,
}

#[trusted]
impl<T> AVec<T> {
    #[spec(fn() -> Self{v: v.len == 0})]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[spec(fn(&Self[@me]) -> usize[me.len])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[spec(fn(&Self[@me]) -> bool[me.len == 0])]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[spec(fn(self: &mut Self[@me], v: T) ensures self : AVec<T>{new: new.len == me.len + 1 && new.elems == arr_set(me.elems, me.len, v)})]
    pub fn push(&mut self, v: T) {
        self.inner.push(v)
    }

    // #[spec(fn(self: &mut Self[@me]) -> T[arr_get(me.elems, me.len - 1)]
    //     requires me.len > 0
    //     ensures  self: Self[{ elems: arr_pop(me.elems), len: me.len - 1 }]
    // )]
    // pub fn pop(&mut self) -> T {
    //     self.inner.pop().unwrap()
    // }

    #[spec(fn(&Self[@me], pos: usize{pos < me.len}) -> &T[arr_get(me.elems, pos)])]
    pub fn get(&self, pos: usize) -> &T {
        self.inner.get(pos).unwrap()
    }

    #[spec(fn(self : &mut Self[@me], pos: usize{pos < me.len}, v: T)
        ensures self : Self[{elems: arr_set(me.elems, pos, v), len: me.len}]
    )]
    pub fn set(&mut self, pos: usize, v: T) {
        self.inner[pos] = v
    }

    pub fn to_vec(self) -> Vec<T> {
        self.inner
    }

    pub fn from_vec(v: Vec<T>) -> Self {
        Self { inner: v }
    }
}

impl<T: Copy> AVec<T> {
    #[proven_externally(proof)]
    #[spec(fn (arr: &AVec<T>[@orig]) -> AVec<T>{v: v.len == orig.len && arr_eq_between(orig.elems, v.elems, 0, v.len)})]
    pub fn copy(arr: &AVec<T>) -> AVec<T> {
        let mut aux = AVec::new();
        let mut i = 0;
        while i < arr.len() {
            aux.push(*arr.get(i));
            i += 1;
        }
        aux
    }
}

impl<T> std::ops::Index<usize> for AVec<T> {
    type Output = T;

    #[trusted_impl]
    #[spec(fn(&AVec<T>[@me], index:usize{index < me.len}) -> &T[arr_get(me.elems, index)])]
    fn index(&self, index: usize) -> &T {
        self.get(index)
    }
}

#[proven_externally(proof)]
pub fn test1() {
    let mut v = AVec::new();
    v.push(10);
    v.push(20);
    v.push(30);
    assert(v[0] == 10);
    assert(v[1] == 20);
    assert(v[2] == 30);
}

#[proven_externally(proof)]
#[spec(fn(n: usize) -> usize[n + 99])]
pub fn canary(n: usize) -> usize {
    n + 99
}
