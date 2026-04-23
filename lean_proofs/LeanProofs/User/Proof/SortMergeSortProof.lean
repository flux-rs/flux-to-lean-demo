import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMergeSort
import LeanProofs.User.Fun.VectorsArrEqBetween
open Classical

namespace F

def mergesort_inv : Int → Arr Int → Int → Arr Int → Int → Arr Int → Int → Prop :=
  fun idx celems clen oelems olen _ _ =>
    0 ≤ idx ∧ idx ≤ olen ∧
    clen = idx ∧
    vectors_arr_eq_between celems oelems 0 idx

open SortMergeSortKVarSolutions

def SortMergeSort_proof : SortMergeSort := by
  unfold SortMergeSort
  exists mergesort_inv ; exists k1
  unfold mergesort_inv k1
  zap
  · split_hyp_ands
    unfold vectors_arr_eq_between at *
    intros i ib
    rename_i i0 aux1 _ _ _ _ _ _ neeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [neeq]
    by_cases i = i0
    · subst i ; simp ; grind
    · simp
      have : i ≠ aux1.len := by grind
      grind
  · grind [sort_is_sorted_between]
end F
