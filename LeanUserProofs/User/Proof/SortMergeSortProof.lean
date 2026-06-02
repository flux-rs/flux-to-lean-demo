import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMergeSort
import LeanProofs.User.Fun.VectorsArrEqBetween
open Classical

namespace F

-- ((k0 (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))) ->

def mergesort_inv (celems : Arr Int) (clen : Int) (idx : Int) (oelems : Arr Int) (olen : Int) (_ : Arr Int) (_ : Int) : Prop :=
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
    rename_i aux1 i0 _ _ _ _ _ _ neeq _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [neeq]
    by_cases i = i0
    · subst i ; simp ; grind
    · simp
      have : i ≠ aux1.len := by grind
      grind
  · grind [sort_is_sorted_between]
end F
