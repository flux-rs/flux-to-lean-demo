import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
open Classical

namespace F

namespace SortInsertionSortKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₃ : (Arr Int)) (a'₄ : Int) (a'₅ : Int) (a'₆ : (Arr Int)) (a'₇ : Int) : Prop :=
  True

end SortInsertionSortKVarSolutions


open SortInsertionSortKVarSolutions




def SortInsertionSort := ∃ k0 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  (0 < (VectorsAVec.len old₀)) ->
   ((VectorsAVec.len old₀) ≥ 0) ->
    (((k0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) 1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀)))) ∧
    (∀ (a'₀ : (VectorsAVec Int)),
     ∀ (n₀ : Int),
      ((k0 (VectorsAVec.elems a'₀) (VectorsAVec.len a'₀) n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀))) ->
       ((VectorsAVec.len a'₀) ≥ 0) ->
        ((¬(n₀ < (VectorsAVec.len a'₀))) ->
         (((VectorsAVec.len a'₀) = (VectorsAVec.len old₀))) ∧
         ((sort_is_sorted_between (VectorsAVec.elems a'₀) 0 (VectorsAVec.len a'₀)))
         ) ∧
        ((n₀ < (VectorsAVec.len a'₀)) ->
         ((sort_is_sorted_between_exc (VectorsAVec.elems a'₀) 0 (n₀ + 1) n₀)) ∧
         ((1 ≤ n₀)) ∧
         (∀ (v₀ : (VectorsAVec Int)),
          (((VectorsAVec.len v₀) = (VectorsAVec.len a'₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (n₀ + 1))) ->
           ((VectorsAVec.len v₀) ≥ 0) ->
            ((k0 (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (n₀ + 1) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))))
         )
        )
    
end F
