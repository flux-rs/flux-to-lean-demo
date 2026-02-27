use crate::vectors::*;
use flux_rs::assert;
use flux_rs::attrs::*;

defs! {
    fn is_sorted(v: Arr<int>) -> prop;
}

#[proven_externally(proof)]
pub fn test1() {
    let mut v = AVec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert(v[0] == 1);
    assert(v[1] == 2);
    assert(v[2] == 3);
}

#[proven_externally(proof)]
#[spec(fn () -> AVec<i32>{ v: is_sorted(v.elems) })]
pub fn test2() -> AVec<i32> {
    let mut v = AVec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v
}

#[proven_externally(proof)]
#[spec(fn(vec: &mut AVec<usize>[@old]) ensures vec: AVec<usize>{v: is_sorted(v.elems) } )]
pub fn init_up(vec: &mut AVec<usize>) {
    let mut i = 0;
    let n = vec.len();
    while i < n {
        vec.set(i, i);
        i += 1;
    }
}

// #[spec(fn(n: usize) -> AVec<usize>{ v: v.len == n })]
// pub fn range(n: usize) -> AVec<usize> {
//     let mut v = AVec::new();
//     let mut i = 0;
//     while i < n {
//         v.push(i);
//         i += 1;
//     }
//     v
// }
