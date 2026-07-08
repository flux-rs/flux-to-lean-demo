import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMergeSort
import LeanProofs.User.Fun.VectorsArrEqBetween
import Flex

open Classical

namespace F

-- ((k0 (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))) ->
@[simp]
def mergesort_inv (celems : Arr Int) (clen : Int) (idx : Int) (oelems : Arr Int) (olen : Int) (_ : Arr Int) (_ : Int) : Prop :=
  0 ≤ idx ∧ idx ≤ olen ∧
  clen = idx ∧
  vectors_arr_eq_between celems oelems 0 idx

def SortMergeSort_proof : SortMergeSort := by
  unfold SortMergeSort
  fusion
  exists mergesort_inv ;
  unfold mergesort_inv
  solve_fixpoint

end F
