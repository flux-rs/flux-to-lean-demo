import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F

namespace SortInsertRecKVarSolutions

-- acyclic (non-cut) kvars
def k3 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₄ : Int) (a'₅ : (Arr Int)) (a'₆ : Int) (a'₇ : Int) (a'₈ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (a'₅ = (VectorsAVec.elems old₀)) ∧ (a'₆ = (VectorsAVec.len old₀)) ∧ (a'₇ = n₀) ∧ (a'₈ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀))
def k4 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₉ : Int) (a'₁₀ : (Arr Int)) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (a'₁₀ = (VectorsAVec.elems old₀)) ∧ (a'₁₁ = (VectorsAVec.len old₀)) ∧ (a'₁₂ = n₀) ∧ (a'₁₃ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀))
def k0 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₁₄ : (Arr Int)) (a'₁₅ : Int) (a'₁₆ : Int) (a'₁₇ : Int) : Prop :=
  ((((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) (k₀ - 1)))) ∧ (a'₁₄ = (VectorsAVec.elems old₀)) ∧ (a'₁₅ = (VectorsAVec.len old₀)) ∧ (a'₁₆ = n₀) ∧ (a'₁₇ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀)) ∨ (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (¬(0 < k₀)) ∧ (a'₁₄ = (VectorsAVec.elems old₀)) ∧ (a'₁₅ = (VectorsAVec.len old₀)) ∧ (a'₁₆ = n₀) ∧ (a'₁₇ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀)))
def k1 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₁₈ : Int) (a'₁₉ : (Arr Int)) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (a'₁₉ = (VectorsAVec.elems old₀)) ∧ (a'₂₀ = (VectorsAVec.len old₀)) ∧ (a'₂₁ = n₀) ∧ (a'₂₂ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀))
def k2 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₂₃ : Int) (a'₂₄ : (Arr Int)) (a'₂₅ : Int) (a'₂₆ : Int) (a'₂₇ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) k₀) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = n₀) ∧ (a'₂₇ = k₀) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀))

end SortInsertRecKVarSolutions


open SortInsertRecKVarSolutions




def SortInsertRec := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k3 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k4 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   ∀ (k₀ : Int),
    (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) k₀) ->
     ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
      (k₀ ≤ n₀) ->
       ((VectorsAVec.len old₀) ≥ 0) ->
        (n₀ ≥ 0) ->
         (k₀ ≥ 0) ->
          ((¬(0 < k₀)) ->
           ((k0 old₀ n₀ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len old₀))) ∧
           (∀ (a'₀ : Int),
            ((k1 old₀ n₀ k₀ a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
           (((k1 old₀ n₀ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
            (∀ (a'₁ : Int),
             ((k2 old₀ n₀ k₀ a'₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
            (((k2 old₀ n₀ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
             ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)))) ->
              ((k0 old₀ n₀ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
              (∀ (a'₂ : Int),
               ((k3 old₀ n₀ k₀ a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
              (((k3 old₀ n₀ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
               (((k₀ - 1) ≥ 0)) ∧
               ((k₀ < (VectorsAVec.len old₀))) ∧
               (∀ (a'₃ : Int),
                ((k4 old₀ n₀ k₀ a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀))) ∧
               (((k4 old₀ n₀ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
                (((k₀ - 1) < (VectorsAVec.len old₀))) ∧
                (((k₀ < (VectorsAVec.len old₀))) ∧
                ((((k₀ - 1) ≥ 0)) ∧
                ((sort_is_sorted_between_exc (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1) (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) k₀)) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (k₀ - 1))) 0 (n₀ + 1) (k₀ - 1))) ∧
                (((k₀ - 1) ≤ n₀))
                )
                )
                )
               )
              )
             )
            )
           ) ∧
          (((k0 old₀ n₀ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀)) ->
           (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems old₀) 0 (n₀ + 1)))
           )
          
end F
