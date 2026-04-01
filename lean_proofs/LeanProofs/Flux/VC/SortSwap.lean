import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet

namespace F

namespace SortSwapKVarSolutions

-- acyclic (non-cut) kvars
def k0 (old₀ : (VectorsAVec Int)) (n₀ : Int) (m_ind₀ : Int) (a'₂ : Int) (a'₃ : (Arr Int)) (a'₄ : Int) (a'₅ : Int) (a'₆ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Bool)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Bool))))) 0)) : ((Int -> (Int -> Bool)))) n₀)) : ((Int -> Bool))) m_ind₀) ∧ (a'₃ = (VectorsAVec.elems old₀)) ∧ (a'₄ = (VectorsAVec.len old₀)) ∧ (a'₅ = m_ind₀) ∧ (a'₆ = n₀) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) m_ind₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) (m_ind₀ - 1))) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀))
def k1 (old₀ : (VectorsAVec Int)) (n₀ : Int) (m_ind₀ : Int) (a'₇ : Int) (a'₈ : (Arr Int)) (a'₉ : Int) (a'₁₀ : Int) (a'₁₁ : Int) : Prop :=
  (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Bool)))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> (Int -> Bool))))) 0)) : ((Int -> (Int -> Bool)))) n₀)) : ((Int -> Bool))) m_ind₀) ∧ (a'₈ = (VectorsAVec.elems old₀)) ∧ (a'₉ = (VectorsAVec.len old₀)) ∧ (a'₁₀ = m_ind₀) ∧ (a'₁₁ = n₀) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) m_ind₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) (m_ind₀ - 1))) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀))

end SortSwapKVarSolutions


open SortSwapKVarSolutions




def SortSwap := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (m_ind₀ : Int),
   ∀ (n₀ : Int),
    ((sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 n₀ m_ind₀) ∧ ((vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) m_ind₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (m_ind₀ - 1)))) ->
     ((0 < m_ind₀) ∧ (m_ind₀ ≤ n₀)) ->
      ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
       ((VectorsAVec.len old₀) ≥ 0) ->
        (m_ind₀ ≥ 0) ->
         (n₀ ≥ 0) ->
          (((m_ind₀ - 1) ≥ 0)) ∧
          (((m_ind₀ - 1) < (VectorsAVec.len old₀))) ∧
          (∀ (a'₀ : Int),
           ((k0 old₀ n₀ m_ind₀ a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) m_ind₀ n₀))) ∧
          (((k0 old₀ n₀ m_ind₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (m_ind₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) m_ind₀ n₀)) ->
           (((m_ind₀ - 1) ≥ 0)) ∧
           ((m_ind₀ < (VectorsAVec.len old₀))) ∧
           (∀ (a'₁ : Int),
            ((k1 old₀ n₀ m_ind₀ a'₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) m_ind₀ n₀))) ∧
           (((k1 old₀ n₀ m_ind₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) m_ind₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) m_ind₀ n₀)) ->
            (((m_ind₀ - 1) < (VectorsAVec.len old₀))) ∧
            (((m_ind₀ < (VectorsAVec.len old₀))) ∧
            ((((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
            ((sort_is_sorted_between_exc (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems old₀) (m_ind₀ - 1) (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) m_ind₀)) m_ind₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) (m_ind₀ - 1))) 0 n₀ (m_ind₀ - 1)))
            )
            )
            )
           )
          
end F
