import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.VectorsArrSet
open Classical

namespace F



def SortTest2 := 
 ∀ (v₀ : (VectorsAVec Int)),
  ((VectorsAVec.len v₀) = 0) ->
   ((VectorsAVec.len v₀) ≥ 0) ->
    ∀ (new₀ : (VectorsAVec Int)),
     (((VectorsAVec.len new₀) = ((VectorsAVec.len v₀) + 1)) ∧ ((VectorsAVec.elems new₀) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) 1))) ->
      ((VectorsAVec.len new₀) ≥ 0) ->
       ∀ (new₁ : (VectorsAVec Int)),
        (((VectorsAVec.len new₁) = ((VectorsAVec.len new₀) + 1)) ∧ ((VectorsAVec.elems new₁) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) 2))) ->
         ((VectorsAVec.len new₁) ≥ 0) ->
          ∀ (new₂ : (VectorsAVec Int)),
           (((VectorsAVec.len new₂) = ((VectorsAVec.len new₁) + 1)) ∧ ((VectorsAVec.elems new₂) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems new₁) (VectorsAVec.len new₁) 3))) ->
            ((VectorsAVec.len new₂) ≥ 0) ->
             (sort_is_sorted_between (VectorsAVec.elems new₂) 0 (VectorsAVec.len new₂))
end F
