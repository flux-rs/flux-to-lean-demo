import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
open Classical

namespace F

namespace SortInsertionSortKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₃ : Int) (a'₄ : (Arr Int)) (a'₅ : Int) (a'₆ : (Arr Int)) (a'₇ : Int) : Prop :=
  ((a'₃ > 0) ∧ (a'₃ ≥ 0) ∧ (a'₃ ≤ a'₅))

end SortInsertionSortKVarSolutions


open SortInsertionSortKVarSolutions




def SortInsertionSort := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  (0 < (VectorsAVec.len old₀)) ->
   ((VectorsAVec.len old₀) ≥ 0) ->
    (((k0 1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀)))) ∧
    (∀ (n₀ : Int),
     ∀ (a'₁ : (VectorsAVec Int)),
      ((k0 n₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))) ->
       ((VectorsAVec.len a'₁) ≥ 0) ->
        ((¬(n₀ < (VectorsAVec.len a'₁))) ->
         (((VectorsAVec.len a'₁) = (VectorsAVec.len old₀))) ∧
         ((sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (VectorsAVec.len a'₁)))
         ) ∧
        ((n₀ < (VectorsAVec.len a'₁)) ->
         ((sort_is_sorted_between_exc (VectorsAVec.elems a'₁) 0 (n₀ + 1) n₀)) ∧
         ((1 ≤ n₀)) ∧
         (∀ (v₀ : (VectorsAVec Int)),
          (((VectorsAVec.len v₀) = (VectorsAVec.len a'₁)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (n₀ + 1))) ->
           ((VectorsAVec.len v₀) ≥ 0) ->
            ((k0 (n₀ + 1) (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))))
         )
        )
    
end F
