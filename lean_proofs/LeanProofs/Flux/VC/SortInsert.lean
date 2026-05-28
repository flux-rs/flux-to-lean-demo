import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F

namespace SortInsertKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₆ : Int) (a'₇ : (Arr Int)) (a'₈ : Int) (a'₉ : (Arr Int)) (a'₁₀ : Int) (a'₁₁ : Int) : Prop :=
  ((a'₆ ≥ 0) ∧ (a'₆ < a'₈) ∧ (a'₆ < a'₁₀) ∧ (a'₆ ≤ a'₈) ∧ (a'₆ ≤ a'₁₀) ∧ (a'₆ ≤ a'₁₁) ∧ (a'₆ ≤ (a'₈ - 1)) ∧ (a'₆ ≤ (a'₁₀ - 1)))
-- acyclic (non-cut) kvars
def k3 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₁ : (VectorsAVec Int)) (a'₁₂ : Int) (a'₁₃ : (Arr Int)) (a'₁₄ : Int) (a'₁₅ : Int) (a'₁₆ : Int) (a'₁₇ : (Arr Int)) (a'₁₈ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₁₃ = (VectorsAVec.elems old₀)) ∧ (a'₁₄ = (VectorsAVec.len old₀)) ∧ (a'₁₅ = n₀) ∧ (a'₁₆ = k₀) ∧ (a'₁₇ = (VectorsAVec.elems a'₁)) ∧ (a'₁₈ = (VectorsAVec.len a'₁)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₁)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₁)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))
def k1 (old₀ : (VectorsAVec Int)) (n₀ : Int) (a'₁ : (VectorsAVec Int)) (k₀ : Int) (a'₁₉ : (Arr Int)) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : Int) (a'₂₃ : (Arr Int)) (a'₂₄ : Int) : Prop :=
  ((((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) (k₀ - 1)))) ∧ (a'₁₉ = (VectorsAVec.elems old₀)) ∧ (a'₂₀ = (VectorsAVec.len old₀)) ∧ (a'₂₁ = n₀) ∧ (a'₂₂ = k₀) ∧ (a'₂₃ = (VectorsAVec.elems a'₁)) ∧ (a'₂₄ = (VectorsAVec.len a'₁)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₁)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₁)) ∧ (k₀ ≤ (VectorsAVec.len old₀))) ∨ (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (¬(0 < k₀)) ∧ (a'₁₉ = (VectorsAVec.elems old₀)) ∧ (a'₂₀ = (VectorsAVec.len old₀)) ∧ (a'₂₁ = n₀) ∧ (a'₂₂ = k₀) ∧ (a'₂₃ = (VectorsAVec.elems a'₁)) ∧ (a'₂₄ = (VectorsAVec.len a'₁)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (k₀ < (VectorsAVec.len a'₁)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₁)) ∧ (k₀ ≤ (VectorsAVec.len old₀))))
def k2 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₁ : (VectorsAVec Int)) (a'₂₅ : Int) (a'₂₆ : (Arr Int)) (a'₂₇ : Int) (a'₂₈ : Int) (a'₂₉ : Int) (a'₃₀ : (Arr Int)) (a'₃₁ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₂₆ = (VectorsAVec.elems old₀)) ∧ (a'₂₇ = (VectorsAVec.len old₀)) ∧ (a'₂₈ = n₀) ∧ (a'₂₉ = k₀) ∧ (a'₃₀ = (VectorsAVec.elems a'₁)) ∧ (a'₃₁ = (VectorsAVec.len a'₁)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₁)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₁)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))

end SortInsertKVarSolutions


open SortInsertKVarSolutions




def SortInsert := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k3 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) n₀) ->
    ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
     ((VectorsAVec.len old₀) ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (k₀ : Int),
        ∀ (a'₁ : (VectorsAVec Int)),
         ((k0 k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
          ((¬(0 < k₀)) ->
           ((k1 old₀ n₀ a'₁ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len a'₁))) ∧
           (∀ (a'₂ : Int),
            ((k2 old₀ n₀ k₀ a'₁ a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
           (((k2 old₀ n₀ k₀ a'₁ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
            (∀ (a'₃ : Int),
             ((k3 old₀ n₀ k₀ a'₁ a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
            (((k3 old₀ n₀ k₀ a'₁ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
             ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)))) ->
              ((k1 old₀ n₀ a'₁ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
              ((k₀ < (VectorsAVec.len a'₁))) ∧
              (((VectorsAVec.len a'₁) ≥ 0) ->
               (((k₀ - 1) ≥ 0)) ∧
               (((k0 (k₀ - 1) (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1) a'₅) k₀ a'₄))) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)))
               )
              )
             )
            )
           ) ∧
          (((k1 old₀ n₀ a'₁ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
           (((VectorsAVec.len a'₁) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (n₀ + 1)))
           )
          )
       
end F
