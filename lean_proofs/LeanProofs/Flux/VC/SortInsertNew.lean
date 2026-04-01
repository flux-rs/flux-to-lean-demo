import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsSortedBetweenExc
import LeanProofs.User.Fun.VectorsArrGet

namespace F

namespace SortInsertNewKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₆ : Int) (a'₇ : (Arr Int)) (a'₈ : Int) (a'₉ : (Arr Int)) (a'₁₀ : Int) (a'₁₁ : Int) : Prop :=
  ((a'₆ ≥ 0) ∧ (a'₆ < a'₈) ∧ (a'₆ < a'₁₀) ∧ (a'₆ ≤ a'₈) ∧ (a'₆ ≤ a'₁₀) ∧ (a'₆ ≤ a'₁₁) ∧ (a'₆ ≤ (a'₈ - 1)) ∧ (a'₆ ≤ (a'₁₀ - 1)))
-- acyclic (non-cut) kvars
def k3 (a'₁ : (VectorsAVec Int)) (n₀ : Int) (m_ind₀ : Int) (old₀ : (VectorsAVec Int)) (a'₁₂ : (Arr Int)) (a'₁₃ : Int) (a'₁₄ : (Arr Int)) (a'₁₅ : Int) (a'₁₆ : Int) (a'₁₇ : Int) (a'₁₈ : (Arr Int)) (a'₁₉ : Int) : Prop :=
  (((∃ (a'₂₀ : (VectorsAVec Int)), (((((((((((((sort_is_sorted_between_exc) : (((Arr Int) -> (Int -> (Int -> (Int -> Bool)))))) (VectorsAVec.elems a'₂₀))) : ((Int -> (Int -> (Int -> Bool))))) 0)) : ((Int -> (Int -> Bool)))) n₀)) : ((Int -> Bool))) (m_ind₀ - 1)) ∧ (a'₁₂ = (VectorsAVec.elems a'₂₀)) ∧ (a'₁₃ = (VectorsAVec.len a'₂₀)) ∧ ((VectorsAVec.len a'₂₀) = (VectorsAVec.len a'₁)) ∧ ((VectorsAVec.len a'₂₀) ≥ 0))) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Bool))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> Bool)))) 0)) : ((Int -> Bool))) n₀) ∧ (a'₁₄ = (VectorsAVec.elems old₀)) ∧ (a'₁₅ = (VectorsAVec.len old₀)) ∧ (a'₁₆ = n₀) ∧ (a'₁₇ = m_ind₀) ∧ (a'₁₈ = (VectorsAVec.elems a'₁)) ∧ (a'₁₉ = (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (m_ind₀ < (VectorsAVec.len a'₁)) ∧ (m_ind₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) m_ind₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) (m_ind₀ - 1))) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀) ∧ (m_ind₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (m_ind₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (m_ind₀ ≤ (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≤ (VectorsAVec.len old₀))) ∨ ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Bool))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> Bool)))) 0)) : ((Int -> Bool))) n₀) ∧ (¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) m_ind₀) < ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₁))) : ((Int -> Int))) (m_ind₀ - 1)))) ∧ (a'₁₂ = (VectorsAVec.elems a'₁)) ∧ (a'₁₃ = (VectorsAVec.len a'₁)) ∧ (a'₁₄ = (VectorsAVec.elems old₀)) ∧ (a'₁₅ = (VectorsAVec.len old₀)) ∧ (a'₁₆ = n₀) ∧ (a'₁₇ = m_ind₀) ∧ (a'₁₈ = (VectorsAVec.elems a'₁)) ∧ (a'₁₉ = (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (m_ind₀ < (VectorsAVec.len a'₁)) ∧ (m_ind₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀) ∧ (m_ind₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (m_ind₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (m_ind₀ ≤ (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≤ (VectorsAVec.len old₀))))
def k1 (old₀ : (VectorsAVec Int)) (n₀ : Int) (m_ind₀ : Int) (a'₁ : (VectorsAVec Int)) (a'₂₁ : Int) (a'₂₂ : (Arr Int)) (a'₂₃ : Int) (a'₂₄ : Int) (a'₂₅ : Int) (a'₂₆ : (Arr Int)) (a'₂₇ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Bool))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> Bool)))) 0)) : ((Int -> Bool))) n₀) ∧ (a'₂₂ = (VectorsAVec.elems old₀)) ∧ (a'₂₃ = (VectorsAVec.len old₀)) ∧ (a'₂₄ = n₀) ∧ (a'₂₅ = m_ind₀) ∧ (a'₂₆ = (VectorsAVec.elems a'₁)) ∧ (a'₂₇ = (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (m_ind₀ < (VectorsAVec.len a'₁)) ∧ (m_ind₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀) ∧ (m_ind₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (m_ind₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (m_ind₀ ≤ (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≤ (VectorsAVec.len old₀)))
def k2 (old₀ : (VectorsAVec Int)) (n₀ : Int) (m_ind₀ : Int) (a'₁ : (VectorsAVec Int)) (a'₂₈ : Int) (a'₂₉ : (Arr Int)) (a'₃₀ : Int) (a'₃₁ : Int) (a'₃₂ : Int) (a'₃₃ : (Arr Int)) (a'₃₄ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Bool))))) (VectorsAVec.elems old₀))) : ((Int -> (Int -> Bool)))) 0)) : ((Int -> Bool))) n₀) ∧ (a'₂₉ = (VectorsAVec.elems old₀)) ∧ (a'₃₀ = (VectorsAVec.len old₀)) ∧ (a'₃₁ = n₀) ∧ (a'₃₂ = m_ind₀) ∧ (a'₃₃ = (VectorsAVec.elems a'₁)) ∧ (a'₃₄ = (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≥ 0) ∧ (n₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (0 < m_ind₀) ∧ (m_ind₀ < (VectorsAVec.len a'₁)) ∧ (m_ind₀ < (VectorsAVec.len old₀)) ∧ (n₀ < (VectorsAVec.len old₀)) ∧ (1 ≤ n₀) ∧ (m_ind₀ ≤ n₀) ∧ (m_ind₀ ≤ ((VectorsAVec.len a'₁) - 1)) ∧ (m_ind₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (m_ind₀ ≤ (VectorsAVec.len a'₁)) ∧ (m_ind₀ ≤ (VectorsAVec.len old₀)))

end SortInsertNewKVarSolutions


open SortInsertNewKVarSolutions




def SortInsertNew := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> Prop, ∃ k3 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (Arr Int)) -> (a11 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   (sort_is_sorted_between (VectorsAVec.elems old₀) 0 n₀) ->
    ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
     ((VectorsAVec.len old₀) ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (m_ind₀ : Int),
        ∀ (a'₁ : (VectorsAVec Int)),
         ((k0 m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
          ((!(0 < m_ind₀)) ->
           (((VectorsAVec.len a'₁) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (n₀ + 1)))
           ) ∧
          ((0 < m_ind₀) ->
           ((m_ind₀ < (VectorsAVec.len a'₁))) ∧
           (∀ (a'₂ : Int),
            ((k1 old₀ n₀ m_ind₀ a'₁ a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
           (((k1 old₀ n₀ m_ind₀ a'₁ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) m_ind₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
            (((m_ind₀ - 1) ≥ 0)) ∧
            (((m_ind₀ - 1) < (VectorsAVec.len a'₁))) ∧
            (∀ (a'₃ : Int),
             ((k2 old₀ n₀ m_ind₀ a'₁ a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
            (((k2 old₀ n₀ m_ind₀ a'₁ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (m_ind₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
             ((!((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) m_ind₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (m_ind₀ - 1)))) ->
              ((k3 a'₁ n₀ m_ind₀ old₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) m_ind₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (m_ind₀ - 1))) ->
              ((sort_is_sorted_between_exc (VectorsAVec.elems a'₁) 0 n₀ m_ind₀)) ∧
              ((m_ind₀ ≤ n₀)) ∧
              ((n₀ < (VectorsAVec.len a'₁))) ∧
              (∀ (v₀ : (VectorsAVec Int)),
               (((VectorsAVec.len v₀) = (VectorsAVec.len a'₁)) ∧ (sort_is_sorted_between_exc (VectorsAVec.elems v₀) 0 n₀ (m_ind₀ - 1))) ->
                ((VectorsAVec.len v₀) ≥ 0) ->
                 ((k3 a'₁ n₀ m_ind₀ old₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))))
              ) ∧
             (∀ (a'₅ : (VectorsAVec Int)),
              ((k3 a'₁ n₀ m_ind₀ old₀ (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ m_ind₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
               (((m_ind₀ - 1) ≥ 0)) ∧
               (((k0 (m_ind₀ - 1) (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)))
               )
             )
            )
           )
          )
       
end F
