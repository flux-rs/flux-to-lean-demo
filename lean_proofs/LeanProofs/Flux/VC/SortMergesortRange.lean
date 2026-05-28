import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrGet
import LeanProofs.User.Fun.VectorsArrEqBetween
open Classical

namespace F

namespace SortMergesortRangeKVarSolutions

-- acyclic (non-cut) kvars
def k0 (v₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (v₃ : (VectorsAVec Int)) (old₀ : (VectorsAVec Int)) (a'₉ : Int) (a'₁₀ : (Arr Int)) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : Int) (a'₁₄ : (Arr Int)) (a'₁₅ : Int) (a'₁₆ : (Arr Int)) (a'₁₇ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₃))) : ((Int -> (Int -> Prop)))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) : ((Int -> Prop))) (hi₀ + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₃))) : ((Int -> (Int -> Prop)))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) : ((Int -> Prop))) hi₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (lo₀ + ((hi₀ - lo₀) / 2))) ∧ (¬(hi₀ ≤ lo₀)) ∧ (a'₁₀ = (VectorsAVec.elems old₀)) ∧ (a'₁₁ = (VectorsAVec.len old₀)) ∧ (a'₁₂ = lo₀) ∧ (a'₁₃ = hi₀) ∧ (a'₁₄ = (VectorsAVec.elems v₀)) ∧ (a'₁₅ = (VectorsAVec.len v₀)) ∧ (a'₁₆ = (VectorsAVec.elems v₃)) ∧ (a'₁₇ = (VectorsAVec.len v₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ ((VectorsAVec.len v₃) = (VectorsAVec.len v₀)) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len v₃) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (lo₀ ≤ hi₀))
def k1 (v₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (v₃ : (VectorsAVec Int)) (old₀ : (VectorsAVec Int)) (a'₁₈ : Int) (a'₁₉ : (Arr Int)) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : Int) (a'₂₃ : (Arr Int)) (a'₂₄ : Int) (a'₂₅ : (Arr Int)) (a'₂₆ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₃))) : ((Int -> (Int -> Prop)))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) : ((Int -> Prop))) (hi₀ + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₃))) : ((Int -> (Int -> Prop)))) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) : ((Int -> Prop))) hi₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (lo₀ + ((hi₀ - lo₀) / 2))) ∧ (¬(hi₀ ≤ lo₀)) ∧ (a'₁₉ = (VectorsAVec.elems old₀)) ∧ (a'₂₀ = (VectorsAVec.len old₀)) ∧ (a'₂₁ = lo₀) ∧ (a'₂₂ = hi₀) ∧ (a'₂₃ = (VectorsAVec.elems v₀)) ∧ (a'₂₄ = (VectorsAVec.len v₀)) ∧ (a'₂₅ = (VectorsAVec.elems v₃)) ∧ (a'₂₆ = (VectorsAVec.len v₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ ((VectorsAVec.len v₃) = (VectorsAVec.len v₀)) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len v₃) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (lo₀ ≤ hi₀))

end SortMergesortRangeKVarSolutions


open SortMergesortRangeKVarSolutions




def SortMergesortRange := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : (VectorsAVec Int)) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (Arr Int)) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : (VectorsAVec Int)) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : (Arr Int)) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     ((lo₀ ≤ hi₀) ∧ (hi₀ < (VectorsAVec.len old₀))) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(hi₀ ≤ lo₀)) ->
          (((hi₀ - lo₀) ≥ 0)) ∧
          ((((lo₀ ≤ (lo₀ + ((hi₀ - lo₀) / 2)))) ∧
          (((lo₀ + ((hi₀ - lo₀) / 2)) < (VectorsAVec.len old₀)))
          ) ∧
          (∀ (v₀ : (VectorsAVec Int)),
           (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₀) lo₀ ((lo₀ + ((hi₀ - lo₀) / 2)) + 1)) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ (lo₀ + ((hi₀ - lo₀) / 2)))) ->
            ((VectorsAVec.len v₀) ≥ 0) ->
             ((((lo₀ + ((hi₀ - lo₀) / 2)) + 1) < (VectorsAVec.len v₀))) ∧
             (((((lo₀ + ((hi₀ - lo₀) / 2)) + 1) ≤ hi₀)) ∧
             ((hi₀ < (VectorsAVec.len v₀)))
             ) ∧
             (∀ (v₁ : (VectorsAVec Int)),
              ((VectorsAVec.len v₁) = (VectorsAVec.len old₀)) ->
               ((VectorsAVec.len v₁) = (VectorsAVec.len v₀))) ∧
             (∀ (v₂ : (VectorsAVec Int)),
              ((VectorsAVec.len v₂) = (VectorsAVec.len v₀)) ->
               ((VectorsAVec.len v₂) = (VectorsAVec.len old₀))) ∧
             (∀ (v₃ : (VectorsAVec Int)),
              (((VectorsAVec.len v₃) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₃) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₃) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1) hi₀)) ->
               ((VectorsAVec.len v₃) ≥ 0) ->
                (((lo₀ + ((hi₀ - lo₀) / 2)) < (VectorsAVec.len v₃))) ∧
                (∀ (a'₄ : Int),
                 ((k0 v₀ lo₀ hi₀ v₃ old₀ a'₄ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems v₃) (VectorsAVec.len v₃)))) ∧
                (((k0 v₀ lo₀ hi₀ v₃ old₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) (lo₀ + ((hi₀ - lo₀) / 2))) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems v₃) (VectorsAVec.len v₃))) ->
                 ((((lo₀ + ((hi₀ - lo₀) / 2)) + 1) < (VectorsAVec.len v₃))) ∧
                 (∀ (a'₅ : Int),
                  ((k1 v₀ lo₀ hi₀ v₃ old₀ a'₅ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems v₃) (VectorsAVec.len v₃)))) ∧
                 (((k1 v₀ lo₀ hi₀ v₃ old₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems v₃) (VectorsAVec.len v₃))) ->
                  ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) (lo₀ + ((hi₀ - lo₀) / 2))) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1)))) ->
                   ∀ (v₄ : (VectorsAVec Int)),
                    ((VectorsAVec.len v₄) = (VectorsAVec.len old₀)) ->
                     ((sort_is_sorted_between (VectorsAVec.elems v₃) lo₀ ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) ∧
                     (((VectorsAVec.len v₄) = (VectorsAVec.len v₃))) ∧
                     ((lo₀ < (VectorsAVec.len v₃))) ∧
                     (((lo₀ ≤ (lo₀ + ((hi₀ - lo₀) / 2)))) ∧
                     (((lo₀ + ((hi₀ - lo₀) / 2)) < (VectorsAVec.len v₃)))
                     ) ∧
                     ((((lo₀ + ((hi₀ - lo₀) / 2)) < hi₀)) ∧
                     ((hi₀ < (VectorsAVec.len v₃)))
                     ) ∧
                     (∀ (v₅ : (VectorsAVec Int)),
                      (((VectorsAVec.len v₅) = (VectorsAVec.len v₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₅) lo₀ (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₃) (VectorsAVec.elems v₅) lo₀ hi₀)) ->
                       ((VectorsAVec.len v₅) ≥ 0) ->
                        ∀ (v₆ : (VectorsAVec Int)),
                         (((VectorsAVec.len v₆) = (VectorsAVec.len v₃)) ∧ (vectors_arr_eq_between (t0 := Int) (VectorsAVec.elems v₃) (VectorsAVec.elems v₆) lo₀ (hi₀ + 1))) ->
                          ((VectorsAVec.len v₆) ≥ 0) ->
                           (((VectorsAVec.len v₆) = (VectorsAVec.len old₀))) ∧
                           ((((VectorsAVec.len v₅) = (VectorsAVec.len old₀))) ∧
                           ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₅) lo₀ hi₀))
                           )
                           )
                     ) ∧
                  (((vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) (lo₀ + ((hi₀ - lo₀) / 2))) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems v₃) ((lo₀ + ((hi₀ - lo₀) / 2)) + 1))) ->
                   (((VectorsAVec.len v₃) = (VectorsAVec.len old₀))) ∧
                   ((sort_is_sorted_between (VectorsAVec.elems v₃) lo₀ (hi₀ + 1))) ∧
                   ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₃) lo₀ hi₀))
                   )
                  )
                 )
                )
             )
          )
          ) ∧
         ((hi₀ ≤ lo₀) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          )
         
end F
