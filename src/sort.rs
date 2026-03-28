use crate::vectors::*;
use flux_rs::assert;
use flux_rs::attrs::*;

defs! {
    fn is_sorted_between(v: Arr<int>, lo: int, hi: int) -> bool;
    fn is_sorted_between_exc(v: Arr<int>, lo: int, hi: int, exc: int) -> bool;
    fn is_sorted(v: AVec<int>) -> bool {
        is_sorted_between(v.elems, 0, v.len)
    }
    fn swap_elems(v: Arr<int>, src: int, dst: int) -> Arr<int> {
        let src_val = arr_get(v, src);
        let dst_val = arr_get(v, dst);
        arr_set(arr_set(v, src, dst_val), dst, src_val)
    }
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
#[spec(fn () -> AVec<i32>{ v: is_sorted(v) })]
pub fn test2() -> AVec<i32> {
    let mut v = AVec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v
}

#[proven_externally(proof)]
#[spec(fn(vec: &mut AVec<usize>[@old]) ensures vec: AVec<usize>{v: is_sorted_between(v.elems, 0, v.len) } )]
pub fn init_up(vec: &mut AVec<usize>) {
    let mut i = 0;
    let n = vec.len();
    while i < n {
        vec.set(i, i);
        i += 1;
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut AVec<i32>[@old], n: usize{1 <= n && n < old.len}, k: usize{k <= n})
       requires is_sorted_between_exc(old.elems, 0, n + 1, k)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, n + 1)})]
fn insert_rec(arr: &mut AVec<i32>, n: usize, k: usize) {
    if 0 < k && arr[k] < arr[k - 1] {
        let tmp = arr[k - 1];
        arr.set(k - 1, arr[k]);
        arr.set(k, tmp);
        insert_rec(arr, n, k - 1)
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut { AVec<i32>[@old] | 1 <= old.len })
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, v.len)})]
pub fn insertion_sort_rec(arr: &mut AVec<i32>) {
    let mut n = 1;
    while n < arr.len() {
        insert_rec(arr, n, n);
        n = n + 1
    }
}

#[spec(fn (arr: &mut AVec<i32>[@old], src: usize{ src < old.len }, dst:usize{dst < old.len})
        requires src != dst
        ensures arr: AVec<i32>[{len: old.len, elems: swap_elems(old.elems, src, dst)}]
 )]
pub fn swap(arr: &mut AVec<i32>, src: usize, dst: usize) {
    let tmp = arr[src];
    arr.set(src, arr[dst]);
    arr.set(dst, tmp);
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut AVec<i32>[@old], n: usize{1 <= n && n < old.len})
       requires is_sorted_between_exc(old.elems, 0, n + 1, n)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, n + 1)})]
fn insert_swap(arr: &mut AVec<i32>, n: usize) {
    let mut k = n;
    while 0 < k && arr[k] < arr[k - 1] {
        swap(arr, k - 1, k);
        k = k - 1;
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut AVec<i32>[@old], n: usize{1 <= n && n < old.len})
       requires is_sorted_between_exc(old.elems, 0, n + 1, n)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, n + 1)})]
fn insert(arr: &mut AVec<i32>, n: usize) {
    let mut k = n;
    while 0 < k && arr[k] < arr[k - 1] {
        let tmp = arr[k - 1];
        arr.set(k - 1, arr[k]);
        arr.set(k, tmp);
        k = k - 1;
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut { AVec<i32>[@old] | 0 < old.len})
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, v.len)})]
pub fn insertion_sort(arr: &mut AVec<i32>) {
    let mut n = 1;
    while n < arr.len() {
        insert(arr, n);
        n = n + 1
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut { AVec<i32>[@me] | is_sorted_between(me.elems, 0, me.len) && 100 < me.len}))]
pub fn test_sorted(arr: &mut AVec<i32>) {
    let a0 = arr[0];
    let a1 = arr[1];
    assert(a0 <= a1);
}

fn partition(arr: &mut AVec<i32>, lo: usize, hi: usize) -> usize {
    todo!()
    // let pivot = arr[hi];
    // let mut i = lo;
    // let mut j = lo;
    // while j < hi {
    //     if arr[j] <= pivot {
    //         let tmp = arr[i];
    //         arr.set(i, arr[j]);
    //         arr.set(j, tmp);
    //         i += 1;
    //     }
    //     j += 1;
    // }
    // let tmp = arr[i];
    // arr.set(i, arr[hi]);
    // arr.set(hi, tmp);
    // i
}

fn quicksort_range(arr: &mut AVec<i32>, lo: usize, hi: usize) {
    if lo < hi {
        let p = partition(arr, lo, hi);
        if p > 0 {
            quicksort_range(arr, lo, p - 1);
        }
        quicksort_range(arr, p + 1, hi);
    }
}

pub fn quicksort(arr: &mut AVec<i32>) {
    let n = arr.len();
    if n > 1 {
        quicksort_range(arr, 0, n - 1);
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn test_insertion_sort() {
        let mut vec = crate::vectors::AVec::from_vec(vec![5, 12, 7, 1, 20, 6]);
        crate::sort::insertion_sort(&mut vec);
        assert!(vec.to_vec() == vec![1, 5, 6, 7, 12, 20]);
    }

    #[test]
    fn test_quicksort() {
        let mut vec = crate::vectors::AVec::from_vec(vec![5, 12, 7, 1, 20, 6]);
        crate::sort::quicksort(&mut vec);
        assert!(vec.to_vec() == vec![1, 5, 6, 7, 12, 20]);
    }
}
