use crate::vectors::*;
use flux_rs::assert;
use flux_rs::attrs::*;

defs! {
    fn is_sorted_between(v: Arr<int>, lo: int, hi: int) -> prop;
    fn is_sorted_between_exc(v: Arr<int>, lo: int, hi: int, exc: int) -> prop;
    fn is_sorted(v: AVec<int>) -> prop {
        is_sorted_between(v.elems, 0, v.len)
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
#[spec(fn (arr: &mut AVec<i32>[@old], m_ind: usize{0 < m_ind && m_ind <= n}, n: usize{1 <= n && n < old.len})
       requires is_sorted_between_exc(old.elems, 0, n, m_ind) &&
                arr_get(old.elems, m_ind) < arr_get(old.elems, m_ind - 1)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between_exc(v.elems, 0, n, m_ind - 1)})]
fn swap(arr: &mut AVec<i32>, m_ind: usize, n: usize) {
    let tmp = arr[m_ind - 1];
    arr.set(m_ind - 1, arr[m_ind]);
    arr.set(m_ind, tmp);
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut AVec<i32>[@old], n: usize{1 <= n && n < old.len})
       requires is_sorted_between(old.elems, 0, n)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, n + 1)})]
fn insert_new(arr: &mut AVec<i32>, n: usize) {
    let mut m_ind = n;
    while 0 < m_ind {
        if arr[m_ind] < arr[m_ind - 1] {
            swap(arr, m_ind, n);
        }
        m_ind = m_ind - 1;
    }
}

#[proven_externally(proof)]
#[spec(fn (arr: &mut AVec<i32>[@old], n: usize{1 <= n && n < old.len})
       requires is_sorted_between(old.elems, 0, n)
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, n + 1)})]
fn insert(arr: &mut AVec<i32>, n: usize) {
    let mut m_ind = n;
    while 0 < m_ind {
        if arr[m_ind] < arr[m_ind - 1] {
            let tmp = arr[m_ind - 1];
            arr.set(m_ind - 1, arr[m_ind]);
            arr.set(m_ind, tmp);
        }
        m_ind = m_ind - 1;
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
#[spec(fn (arr: &mut { AVec<i32>[@old] | 0 < old.len})
       ensures arr: AVec<i32>{v: v.len == old.len && is_sorted_between(v.elems, 0, v.len)})]
pub fn insertion_sort(arr: &mut AVec<i32>) {
    let mut n = 1;
    while n < arr.len() {
        // insert(arr, n);
        insert_rec(arr, n, n);
        n = n + 1
    }
}

/*
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arrOld.toMultiset
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return
*/

#[cfg(test)]
mod test {
    use crate::sort::insertion_sort;

    #[test]
    fn test_insertion_sort() {
        let mut vec = crate::vectors::AVec::from_vec(vec![5, 12, 7, 1, 20, 6]);
        insertion_sort(&mut vec);
        assert!(vec.to_vec() == vec![1, 5, 6, 7, 12, 20]);
    }
}
