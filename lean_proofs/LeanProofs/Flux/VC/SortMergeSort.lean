import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F

namespace SortMergeSortKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₇ : Int) (a'₈ : (Arr Int)) (a'₉ : Int) (a'₁₀ : (Arr Int)) (a'₁₁ : Int) (a'₁₂ : (Arr Int)) (a'₁₃ : Int) : Prop :=
  ((a'₇ = a'₉) ∧ (a'₇ ≥ 0) ∧ (a'₇ ≥ a'₉) ∧ (a'₇ ≥ a'₁₃) ∧ (a'₇ ≤ a'₉) ∧ (a'₇ ≤ a'₁₁))
-- acyclic (non-cut) kvars
def k1 (old₀ : (VectorsAVec Int)) (aux₀ : (VectorsAVec Int)) (i₀ : Int) (aux₁ : (VectorsAVec Int)) (a'₁₄ : Int) (a'₁₅ : (Arr Int)) (a'₁₆ : Int) (a'₁₇ : (Arr Int)) (a'₁₈ : Int) (a'₁₉ : Int) (a'₂₀ : (Arr Int)) (a'₂₁ : Int) : Prop :=
  ((¬((VectorsAVec.len old₀) ≤ 1)) ∧ (a'₁₅ = (VectorsAVec.elems old₀)) ∧ (a'₁₆ = (VectorsAVec.len old₀)) ∧ (a'₁₇ = (VectorsAVec.elems aux₀)) ∧ (a'₁₈ = (VectorsAVec.len aux₀)) ∧ (a'₁₉ = i₀) ∧ (a'₂₀ = (VectorsAVec.elems aux₁)) ∧ (a'₂₁ = (VectorsAVec.len aux₁)) ∧ (i₀ = (VectorsAVec.len aux₁)) ∧ ((VectorsAVec.len aux₀) = 0) ∧ (i₀ ≥ 0) ∧ (i₀ ≥ (VectorsAVec.len aux₀)) ∧ (i₀ ≥ (VectorsAVec.len aux₁)) ∧ ((VectorsAVec.len aux₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (i₀ < (VectorsAVec.len old₀)) ∧ (i₀ ≤ (VectorsAVec.len aux₁)) ∧ (i₀ ≤ (VectorsAVec.len old₀)))

end SortMergeSortKVarSolutions


open SortMergeSortKVarSolutions




def SortMergeSort := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : (VectorsAVec Int)) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : (Arr Int)) -> (a11 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ((VectorsAVec.len old₀) ≥ 0) ->
   ((¬((VectorsAVec.len old₀) ≤ 1)) ->
    ∀ (aux₀ : (VectorsAVec Int)),
     ((VectorsAVec.len aux₀) = 0) ->
      ((VectorsAVec.len aux₀) ≥ 0) ->
       (((k0 0 (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀)))) ∧
       (∀ (i₀ : Int),
        ∀ (aux₁ : (VectorsAVec Int)),
         ((k0 i₀ (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))) ->
          ((¬(i₀ < (VectorsAVec.len old₀))) ->
           ((((VectorsAVec.len old₀) - 1) ≥ 0)) ∧
           ((0 < (VectorsAVec.len old₀))) ∧
           (((0 ≤ ((VectorsAVec.len old₀) - 1))) ∧
           ((((VectorsAVec.len old₀) - 1) < (VectorsAVec.len old₀)))
           ) ∧
           (((VectorsAVec.len aux₁) = (VectorsAVec.len old₀))) ∧
           (∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (((VectorsAVec.len old₀) - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) 0 ((VectorsAVec.len old₀) - 1))) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              ∀ (v₁ : (VectorsAVec Int)),
               ((VectorsAVec.len v₁) ≥ 0) ->
                ((VectorsAVec.len v₁) = (VectorsAVec.len old₀)) ->
                 (sort_is_sorted_between (VectorsAVec.elems v₀) 0 (VectorsAVec.len v₀)))
           ) ∧
          ((i₀ < (VectorsAVec.len old₀)) ->
           (∀ (a'₅ : Int),
            ((k1 old₀ aux₀ i₀ aux₁ a'₅ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) i₀ (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁)))) ∧
           (((k1 old₀ aux₀ i₀ aux₁ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) i₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀) i₀ (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁))) ->
            ∀ (new₀ : (VectorsAVec Int)),
             (((VectorsAVec.len new₀) = ((VectorsAVec.len aux₁) + 1)) ∧ ((VectorsAVec.elems new₀) = (vectors_arr_set (t0 := Int) (VectorsAVec.elems aux₁) (VectorsAVec.len aux₁) (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) i₀)))) ->
              ((VectorsAVec.len new₀) ≥ 0) ->
               ((k0 (i₀ + 1) (VectorsAVec.elems new₀) (VectorsAVec.len new₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems aux₀) (VectorsAVec.len aux₀))))
           )
          )
       ) ∧
   (((VectorsAVec.len old₀) ≤ 1) ->
    (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
    ((sort_is_sorted_between (VectorsAVec.elems old₀) 0 (VectorsAVec.len old₀)))
    )
   
end F
