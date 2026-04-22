use crate::vectors::*;
use flux_rs::attrs::*;



#[cfg(test)]
mod test {
    #[test]
    fn test_merge_sort() {
        let mut vec = crate::vectors::AVec::from_vec(vec![5, 12, 7, 1, 20, 6]);
        crate::sort::merge_sort(&mut vec);
        assert!(vec.to_vec() == vec![1, 5, 6, 7, 12, 20]);
    }
}
