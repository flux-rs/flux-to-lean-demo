import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPartitionedBy
import LeanProofs.User.Fun.SortIsPerm
open Classical

namespace F

namespace SortQuicksortRangeKVarSolutions

-- acyclic (non-cut) kvars
def k0 (lo₀ : Int) (p₀ : Int) (v₀ : (VectorsAVec Int)) (hi₀ : Int) (old₀ : (VectorsAVec Int)) (a'₆ : (Arr Int)) (a'₇ : Int) (a'₈ : (Arr Int)) (a'₉ : Int) (a'₁₀ : Int) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : (Arr Int)) (a'₁₄ : Int) : Prop :=
  (((∃ (a'₁₅ : (VectorsAVec Int)), ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₁₅))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₁₅))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ (a'₆ = (VectorsAVec.elems a'₁₅)) ∧ (a'₇ = (VectorsAVec.len a'₁₅)) ∧ ((VectorsAVec.len a'₁₅) = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len a'₁₅) ≥ 0))) ∧ (((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (a'₈ = (VectorsAVec.elems old₀)) ∧ (a'₉ = (VectorsAVec.len old₀)) ∧ (a'₁₀ = lo₀) ∧ (a'₁₁ = hi₀) ∧ (a'₁₂ = p₀) ∧ (a'₁₃ = (VectorsAVec.elems v₀)) ∧ (a'₁₄ = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < p₀) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)) ∨ ((((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (¬(lo₀ < p₀)) ∧ (a'₆ = (VectorsAVec.elems v₀)) ∧ (a'₇ = (VectorsAVec.len v₀)) ∧ (a'₈ = (VectorsAVec.elems old₀)) ∧ (a'₉ = (VectorsAVec.len old₀)) ∧ (a'₁₀ = lo₀) ∧ (a'₁₁ = hi₀) ∧ (a'₁₂ = p₀) ∧ (a'₁₃ = (VectorsAVec.elems v₀)) ∧ (a'₁₄ = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)))
def k1 (p₀ : Int) (hi₀ : Int) (a'₃ : (VectorsAVec Int)) (v₀ : (VectorsAVec Int)) (lo₀ : Int) (old₀ : (VectorsAVec Int)) (a'₁₆ : (Arr Int)) (a'₁₇ : Int) (a'₁₈ : (Arr Int)) (a'₁₉ : Int) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : Int) (a'₂₃ : (Arr Int)) (a'₂₄ : Int) (a'₂₅ : (Arr Int)) (a'₂₆ : Int) : Prop :=
  (((∃ (a'₂₇ : (VectorsAVec Int)), ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₇))) : ((Int -> (Int -> Prop)))) (p₀ + 1))) : ((Int -> Prop))) (hi₀ + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems a'₃))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₇))) : ((Int -> (Int -> Prop)))) (p₀ + 1))) : ((Int -> Prop))) hi₀) ∧ (a'₁₆ = (VectorsAVec.elems a'₂₇)) ∧ (a'₁₇ = (VectorsAVec.len a'₂₇)) ∧ ((VectorsAVec.len a'₂₇) = (VectorsAVec.len a'₃)) ∧ ((VectorsAVec.len a'₂₇) ≥ 0))) ∧ (((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (((∃ (a'₂₈ : (VectorsAVec Int)), (((VectorsAVec.len a'₂₈) = (VectorsAVec.len v₀)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₈))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₈))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ ((VectorsAVec.len a'₂₈) ≥ 0) ∧ ((VectorsAVec.len a'₂₈) ≥ 0) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems a'₂₈)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len a'₂₈)))) ∧ (lo₀ < p₀)) ∨ ((¬(lo₀ < p₀)) ∧ (¬(lo₀ < p₀)) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems v₀)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len v₀)))) ∧ (a'₂₆ = (VectorsAVec.len a'₃)) ∧ (a'₁₈ = (VectorsAVec.elems old₀)) ∧ (a'₁₉ = (VectorsAVec.len old₀)) ∧ (a'₂₀ = lo₀) ∧ (a'₂₁ = hi₀) ∧ (a'₂₂ = p₀) ∧ (a'₂₃ = (VectorsAVec.elems v₀)) ∧ (a'₂₄ = (VectorsAVec.len v₀)) ∧ (a'₂₅ = (VectorsAVec.elems a'₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (p₀ < hi₀) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)) ∨ ((((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (((∃ (a'₂₉ : (VectorsAVec Int)), (((VectorsAVec.len a'₂₉) = (VectorsAVec.len v₀)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₉))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₉))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ ((VectorsAVec.len a'₂₉) ≥ 0) ∧ ((VectorsAVec.len a'₂₉) ≥ 0) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems a'₂₉)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len a'₂₉)))) ∧ (lo₀ < p₀)) ∨ ((¬(lo₀ < p₀)) ∧ (¬(lo₀ < p₀)) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems v₀)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len v₀)))) ∧ (¬(p₀ < hi₀)) ∧ (a'₁₆ = (VectorsAVec.elems a'₃)) ∧ (a'₁₇ = (VectorsAVec.len a'₃)) ∧ (a'₂₆ = (VectorsAVec.len a'₃)) ∧ (a'₁₈ = (VectorsAVec.elems old₀)) ∧ (a'₁₉ = (VectorsAVec.len old₀)) ∧ (a'₂₀ = lo₀) ∧ (a'₂₁ = hi₀) ∧ (a'₂₂ = p₀) ∧ (a'₂₃ = (VectorsAVec.elems v₀)) ∧ (a'₂₄ = (VectorsAVec.len v₀)) ∧ (a'₂₅ = (VectorsAVec.elems a'₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)))

end SortQuicksortRangeKVarSolutions


open SortQuicksortRangeKVarSolutions




def SortQuicksortRange := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (VectorsAVec Int)) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (VectorsAVec Int)) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> (a15 : (Arr Int)) -> (a16 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     (hi₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(lo₀ < hi₀)) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          ) ∧
         ((lo₀ < hi₀) ->
          ∀ (p₀ : Int),
           ∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_partitioned_by (VectorsAVec.elems v₀) lo₀ p₀ (hi₀ + 1) p₀) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ hi₀) ∧ (lo₀ ≤ p₀) ∧ (p₀ ≤ hi₀)) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (p₀ ≥ 0) ->
               ((¬(lo₀ < p₀)) ->
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
               ((lo₀ < p₀) ->
                (((p₀ - 1) ≥ 0)) ∧
                ((lo₀ < (VectorsAVec.len v₀))) ∧
                (((p₀ - 1) < (VectorsAVec.len v₀))) ∧
                (∀ (v₁ : (VectorsAVec Int)),
                 (((VectorsAVec.len v₁) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₁) lo₀ ((p₀ - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₁) lo₀ (p₀ - 1))) ->
                  ((VectorsAVec.len v₁) ≥ 0) ->
                   ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₁) (VectorsAVec.len v₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                ) ∧
               (∀ (a'₃ : (VectorsAVec Int)),
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                 ((¬(p₀ < hi₀)) ->
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                 ((p₀ < hi₀) ->
                  (((p₀ + 1) < (VectorsAVec.len a'₃))) ∧
                  ((hi₀ < (VectorsAVec.len a'₃))) ∧
                  (∀ (v₂ : (VectorsAVec Int)),
                   (((VectorsAVec.len v₂) = (VectorsAVec.len a'₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₂) (p₀ + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems a'₃) (VectorsAVec.elems v₂) (p₀ + 1) hi₀)) ->
                    ((VectorsAVec.len v₂) ≥ 0) ->
                     ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems v₂) (VectorsAVec.len v₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                  ) ∧
                 (∀ (a'₅ : (VectorsAVec Int)),
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   (((VectorsAVec.len a'₅) = (VectorsAVec.len old₀))) ∧
                   ((sort_is_sorted_between (VectorsAVec.elems a'₅) lo₀ (hi₀ + 1))) ∧
                   ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₅) lo₀ hi₀))
                   )
                 )
               )
         
end F
