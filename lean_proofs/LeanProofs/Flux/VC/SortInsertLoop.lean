import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet

namespace F

namespace SortInsertLoopKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₁₀ : Int) (a'₁₁ : (Arr Int)) (a'₁₂ : Int) (a'₁₃ : (Arr Int)) (a'₁₄ : Int) (a'₁₅ : Int) : Prop :=
  ((a'₁₀ ≥ 0) ∧ (a'₁₀ < a'₁₂) ∧ (a'₁₀ < a'₁₄) ∧ (a'₁₀ ≤ a'₁₂) ∧ (a'₁₀ ≤ a'₁₄) ∧ (a'₁₀ ≤ a'₁₅) ∧ (a'₁₀ ≤ (a'₁₂ - 1)) ∧ (a'₁₀ ≤ (a'₁₄ - 1)))
def k1 (a'₁₆ : Int) (a'₁₇ : Int) (a'₁₈ : (Arr Int)) (a'₁₉ : Int) (a'₂₀ : (Arr Int)) (a'₂₁ : Int) (a'₂₂ : Int) : Prop :=
  True
-- acyclic (non-cut) kvars
def k6 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₂ : (VectorsAVec Int)) (a'₂₃ : Int) (a'₂₄ : (Arr Int)) (a'₂₅ : Int) (a'₂₆ : Int) (a'₂₇ : Int) (a'₂₈ : (Arr Int)) (a'₂₉ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = n₀) ∧ (a'₂₇ = k₀) ∧ (a'₂₈ = (VectorsAVec.elems a'₂)) ∧ (a'₂₉ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))
def k3 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₂ : (VectorsAVec Int)) (a'₃₀ : Int) (a'₃₁ : (Arr Int)) (a'₃₂ : Int) (a'₃₃ : Int) (a'₃₄ : Int) (a'₃₅ : (Arr Int)) (a'₃₆ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₃₁ = (VectorsAVec.elems old₀)) ∧ (a'₃₂ = (VectorsAVec.len old₀)) ∧ (a'₃₃ = n₀) ∧ (a'₃₄ = k₀) ∧ (a'₃₅ = (VectorsAVec.elems a'₂)) ∧ (a'₃₆ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))
def k8 (old₀ : (VectorsAVec Int)) (n₀ : Int) (a'₂ : (VectorsAVec Int)) (k₀ : Int) (a'₃₇ : Int) (a'₃₈ : (Arr Int)) (a'₃₉ : Int) (a'₄₀ : Int) (a'₄₁ : Int) (a'₄₂ : (Arr Int)) (a'₄₃ : Int) : Prop :=
  ((((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₃₇ = ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (a'₃₈ = (VectorsAVec.elems old₀)) ∧ (a'₃₉ = (VectorsAVec.len old₀)) ∧ (a'₄₀ = n₀) ∧ (a'₄₁ = k₀) ∧ (a'₄₂ = (VectorsAVec.elems a'₂)) ∧ (a'₄₃ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len a'₂) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))) ∨ (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ ((a'₃₇ = ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀)) ∨ True) ∧ (a'₃₈ = (VectorsAVec.elems old₀)) ∧ (a'₃₉ = (VectorsAVec.len old₀)) ∧ (a'₄₀ = n₀) ∧ (a'₄₁ = k₀) ∧ (a'₄₂ = (VectorsAVec.elems a'₂)) ∧ (a'₄₃ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len a'₂) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))))
def k5 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₂ : (VectorsAVec Int)) (a'₄₄ : Int) (a'₄₅ : (Arr Int)) (a'₄₆ : Int) (a'₄₇ : Int) (a'₄₈ : Int) (a'₄₉ : (Arr Int)) (a'₅₀ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₄₅ = (VectorsAVec.elems old₀)) ∧ (a'₄₆ = (VectorsAVec.len old₀)) ∧ (a'₄₇ = n₀) ∧ (a'₄₈ = k₀) ∧ (a'₄₉ = (VectorsAVec.elems a'₂)) ∧ (a'₅₀ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))
def k4 (old₀ : (VectorsAVec Int)) (n₀ : Int) (k₀ : Int) (a'₂ : (VectorsAVec Int)) (a'₅₁ : Int) (a'₅₂ : (Arr Int)) (a'₅₃ : Int) (a'₅₄ : Int) (a'₅₅ : Int) (a'₅₆ : (Arr Int)) (a'₅₇ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₅₂ = (VectorsAVec.elems old₀)) ∧ (a'₅₃ = (VectorsAVec.len old₀)) ∧ (a'₅₄ = n₀) ∧ (a'₅₅ = k₀) ∧ (a'₅₆ = (VectorsAVec.elems a'₂)) ∧ (a'₅₇ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀)))
def k7 (old₀ : (VectorsAVec Int)) (n₀ : Int) (a'₂ : (VectorsAVec Int)) (k₀ : Int) (a'₅₈ : Int) (a'₅₉ : (Arr Int)) (a'₆₀ : Int) (a'₆₁ : Int) (a'₆₂ : Int) (a'₆₃ : (Arr Int)) (a'₆₄ : Int) : Prop :=
  ((((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₅₈ = ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀)) ∧ (a'₅₉ = (VectorsAVec.elems old₀)) ∧ (a'₆₀ = (VectorsAVec.len old₀)) ∧ (a'₆₁ = n₀) ∧ (a'₆₂ = k₀) ∧ (a'₆₃ = (VectorsAVec.elems a'₂)) ∧ (a'₆₄ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))) ∨ (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (a'₅₉ = (VectorsAVec.elems old₀)) ∧ (a'₆₀ = (VectorsAVec.len old₀)) ∧ (a'₆₁ = n₀) ∧ (a'₆₂ = k₀) ∧ (a'₆₃ = (VectorsAVec.elems a'₂)) ∧ (a'₆₄ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1))) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))))
def k2 (old₀ : (VectorsAVec Int)) (n₀ : Int) (a'₂ : (VectorsAVec Int)) (k₀ : Int) (a'₆₅ : (Arr Int)) (a'₆₆ : Int) (a'₆₇ : Int) (a'₆₈ : Int) (a'₆₉ : (Arr Int)) (a'₇₀ : Int) : Prop :=
  ((((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) k₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) (k₀ - 1)))) ∧ (a'₆₅ = (VectorsAVec.elems old₀)) ∧ (a'₆₆ = (VectorsAVec.len old₀)) ∧ (a'₆₇ = n₀) ∧ (a'₆₈ = k₀) ∧ (a'₆₉ = (VectorsAVec.elems a'₂)) ∧ (a'₇₀ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < k₀) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))) ∨ (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Prop))))) 0)) : ((Int -> (Int -> Prop)))) (n₀ + 1))) : ((Int -> Prop))) n₀) ∧ (¬(0 < k₀)) ∧ (a'₆₅ = (VectorsAVec.elems old₀)) ∧ (a'₆₆ = (VectorsAVec.len old₀)) ∧ (a'₆₇ = n₀) ∧ (a'₆₈ = k₀) ∧ (a'₆₉ = (VectorsAVec.elems a'₂)) ∧ (a'₇₀ = (VectorsAVec.len a'₂)) ∧ (k₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (k₀ < (VectorsAVec.len a'₂)) ∧ (k₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (k₀ ≤ n₀) ∧ (k₀ ≤ ((VectorsAVec.len a'₂) - 1)) ∧ (k₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (k₀ ≤ (VectorsAVec.len a'₂)) ∧ (k₀ ≤ (VectorsAVec.len old₀))))

end SortInsertLoopKVarSolutions


open SortInsertLoopKVarSolutions




def SortInsertLoop := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> Prop, ∃ k3 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k4 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k5 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k6 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k7 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k8 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop,
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) n₀) ->
    ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
     ((VectorsAVec.len old₀) ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (a'₀ : Int),
        ((k1 a'₀ n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (k₀ : Int),
        ∀ (a'₂ : (VectorsAVec Int)),
         ((k0 k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
          ((!(0 < k₀)) ->
           ((k2 old₀ n₀ a'₂ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len a'₂))) ∧
           (∀ (a'₃ : Int),
            ((k1 a'₃ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
             ((k3 old₀ n₀ k₀ a'₂ a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
           (((k3 old₀ n₀ k₀ a'₂ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len a'₂))) ∧
            (∀ (a'₄ : Int),
             ((k1 a'₄ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
              ((k4 old₀ n₀ k₀ a'₂ a'₄ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
            (((k4 old₀ n₀ k₀ a'₂ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
             ((!((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1)))) ->
              ((k2 old₀ n₀ a'₂ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len a'₂))) ∧
              (∀ (a'₅ : Int),
               ((k1 a'₅ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
                ((k5 old₀ n₀ k₀ a'₂ a'₅ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
              (((k5 old₀ n₀ k₀ a'₂ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
               (((k₀ - 1) ≥ 0)) ∧
               ((k₀ < (VectorsAVec.len a'₂))) ∧
               (∀ (a'₆ : Int),
                ((k1 a'₆ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
                 ((k6 old₀ n₀ k₀ a'₂ a'₆ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
               (((k6 old₀ n₀ k₀ a'₂ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
                (((k₀ - 1) < (VectorsAVec.len a'₂))) ∧
                (∀ (a'₇ : Int),
                 ((k1 a'₇ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
                  ((k7 old₀ n₀ a'₂ k₀ a'₇ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
                (((k7 old₀ n₀ a'₂ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
                (((VectorsAVec.len a'₂) ≥ 0) ->
                 ((k₀ < (VectorsAVec.len a'₂))) ∧
                 (∀ (a'₈ : Int),
                  ((k7 old₀ n₀ a'₂ k₀ a'₈ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
                   ((k8 old₀ n₀ a'₂ k₀ a'₈ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
                 (((k8 old₀ n₀ a'₂ k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂)))) ∧
                 ((((k₀ - 1) ≥ 0)) ∧
                 (((k0 (k₀ - 1) (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1) (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀)) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1))) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
                 (∀ (a'₉ : Int),
                  ((k8 old₀ n₀ a'₂ k₀ a'₉ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
                   ((k1 a'₉ (k₀ - 1) (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1) (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) k₀)) k₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) (k₀ - 1))) (VectorsAVec.len a'₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)))
                 )
                 )
                )
               )
              )
             )
            )
           ) ∧
          (((k2 old₀ n₀ a'₂ k₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂))) ->
           (((VectorsAVec.len a'₂) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems a'₂) 0 (n₀ + 1)))
           )
          )

end F
