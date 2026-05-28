import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPerm
open Classical

namespace F



def SortQuicksort := 
 ∀ (old₀ : (VectorsAVec Int)),
  ((VectorsAVec.len old₀) ≥ 0) ->
   ((¬((VectorsAVec.len old₀) > 1)) ->
    (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
    ((sort_is_sorted_between (VectorsAVec.elems old₀) 0 (VectorsAVec.len old₀)))
    ) ∧
   (((VectorsAVec.len old₀) > 1) ->
    ((((VectorsAVec.len old₀) - 1) ≥ 0)) ∧
    ((0 < (VectorsAVec.len old₀))) ∧
    ((((VectorsAVec.len old₀) - 1) < (VectorsAVec.len old₀))) ∧
    (∀ (v₀ : (VectorsAVec Int)),
     (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (((VectorsAVec.len old₀) - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) 0 ((VectorsAVec.len old₀) - 1))) ->
      ((VectorsAVec.len v₀) ≥ 0) ->
       (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (VectorsAVec.len v₀)))
    )
   
end F
