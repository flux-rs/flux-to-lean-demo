import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsPartitionedBy
import LeanProofs.User.Fun.SortIsPerm
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F

namespace SortPartitionKVarSolutions

-- cyclic (cut) kvars
def k1 (a'₁₃ : Int) (a'₁₄ : (Arr Int)) (a'₁₅ : Int) (a'₁₆ : Int) (a'₁₇ : (Arr Int)) (a'₁₈ : Int) (a'₁₉ : Int) (a'₂₀ : Int) : Prop :=
  ((a'₁₃ ≥ 0) ∧ (a'₁₃ ≥ a'₁₆) ∧ (a'₁₃ ≥ a'₁₉) ∧ (a'₁₃ < a'₁₈) ∧ (a'₁₃ ≤ a'₁₈) ∧ (a'₁₃ ≤ a'₂₀) ∧ (a'₁₃ ≤ (a'₁₈ - 1)))
-- acyclic (non-cut) kvars
def k3 (a'₂ : (VectorsAVec Int)) (i₀ : Int) (j₀ : Int) (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (a'₂₁ : (Arr Int)) (a'₂₂ : Int) (a'₂₃ : Int) (a'₂₄ : (Arr Int)) (a'₂₅ : Int) (a'₂₆ : Int) (a'₂₇ : Int) (a'₂₈ : Int) (a'₂₉ : (Arr Int)) (a'₃₀ : Int) (a'₃₁ : Int) : Prop :=
  (((a'₂₁ = (let a'₉ := ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) i₀); (let a'₁₀ := ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) j₀); (((((((((vectors_arr_set) : (((Arr Int) -> (Int -> (Int -> (Arr Int)))))) (((((((((vectors_arr_set) : (((Arr Int) -> (Int -> (Int -> (Arr Int)))))) (VectorsAVec.elems a'₂))) : ((Int -> (Int -> (Arr Int))))) i₀)) : ((Int -> (Arr Int)))) a'₁₀))) : ((Int -> (Int -> (Arr Int))))) j₀)) : ((Int -> (Arr Int)))) a'₉)))) ∧ (a'₂₂ = (VectorsAVec.len a'₂)) ∧ (a'₃₁ = i₀) ∧ (a'₂₃ = (i₀ + 1)) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = lo₀) ∧ (a'₂₇ = hi₀) ∧ (a'₂₈ = j₀) ∧ (a'₂₉ = (VectorsAVec.elems a'₂)) ∧ (a'₃₀ = (VectorsAVec.len a'₂)) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len a'₂) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) j₀) ≤ ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) hi₀))) ∨ ((¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₂))) : ((Int -> Int))) j₀) ≤ ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) hi₀))) ∧ (a'₂₁ = (VectorsAVec.elems a'₂)) ∧ (a'₂₂ = (VectorsAVec.len a'₂)) ∧ (a'₃₁ = i₀) ∧ (a'₂₃ = i₀) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = lo₀) ∧ (a'₂₇ = hi₀) ∧ (a'₂₈ = j₀) ∧ (a'₂₉ = (VectorsAVec.elems a'₂)) ∧ (a'₃₀ = (VectorsAVec.len a'₂)) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀))))
def k0 (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (a'₃₂ : Int) (a'₃₃ : (Arr Int)) (a'₃₄ : Int) (a'₃₅ : Int) (a'₃₆ : Int) : Prop :=
  ((a'₃₃ = (VectorsAVec.elems old₀)) ∧ (a'₃₄ = (VectorsAVec.len old₀)) ∧ (a'₃₅ = lo₀) ∧ (a'₃₆ = hi₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)))
def k2 (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (j₀ : Int) (a'₂ : (VectorsAVec Int)) (i₀ : Int) (a'₃₇ : Int) (a'₃₈ : (Arr Int)) (a'₃₉ : Int) (a'₄₀ : Int) (a'₄₁ : Int) (a'₄₂ : Int) (a'₄₃ : (Arr Int)) (a'₄₄ : Int) (a'₄₅ : Int) : Prop :=
  ((a'₃₈ = (VectorsAVec.elems old₀)) ∧ (a'₃₉ = (VectorsAVec.len old₀)) ∧ (a'₄₀ = lo₀) ∧ (a'₄₁ = hi₀) ∧ (a'₄₂ = j₀) ∧ (a'₄₃ = (VectorsAVec.elems a'₂)) ∧ (a'₄₄ = (VectorsAVec.len a'₂)) ∧ (a'₄₅ = i₀) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀)))

end SortPartitionKVarSolutions


open SortPartitionKVarSolutions




def SortPartition := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (VectorsAVec Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : (Arr Int)) -> (a15 : Int) -> (a16 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     ((lo₀ < hi₀) ∧ (hi₀ < (VectorsAVec.len old₀))) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         (∀ (a'₀ : Int),
          ((k0 old₀ lo₀ hi₀ a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀))) ∧
         (((k0 old₀ lo₀ hi₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->
          (((k1 lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀))) ∧
          (∀ (j₀ : Int),
           ∀ (a'₂ : (VectorsAVec Int)),
            ∀ (i₀ : Int),
             ((k1 j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->
              ((¬(j₀ < hi₀)) ->
               ((i₀ < (VectorsAVec.len a'₂))) ∧
               ((hi₀ < (VectorsAVec.len a'₂))) ∧
               (((VectorsAVec.len a'₂) ≥ 0) ->
                (((VectorsAVec.len a'₂) = (VectorsAVec.len old₀))) ∧
                ((sort_is_partitioned_by (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) i₀); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₂) i₀ a'₅) hi₀ a'₄))) lo₀ i₀ hi₀ i₀)) ∧
                ((sort_is_perm (VectorsAVec.elems old₀) (let a'₆ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) i₀); (let a'₇ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₂) i₀ a'₇) hi₀ a'₆))) lo₀ hi₀)) ∧
                ((lo₀ ≤ i₀)) ∧
                ((i₀ ≤ hi₀))
                )
               ) ∧
              ((j₀ < hi₀) ->
               ((j₀ < (VectorsAVec.len a'₂))) ∧
               (∀ (a'₈ : Int),
                ((k2 old₀ lo₀ hi₀ j₀ a'₂ i₀ a'₈ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀))) ∧
               (((k2 old₀ lo₀ hi₀ j₀ a'₂ i₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀)) ->
                ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀))) ->
                 ((k3 a'₂ i₀ j₀ old₀ lo₀ hi₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀))) ∧
                (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀)) ->
                 ((i₀ < (VectorsAVec.len a'₂))) ∧
                 ((j₀ < (VectorsAVec.len a'₂))) ∧
                 (((VectorsAVec.len a'₂) ≥ 0) ->
                  ((k3 a'₂ i₀ j₀ old₀ lo₀ hi₀ (let a'₉ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) i₀); (let a'₁₀ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₂) j₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₂) i₀ a'₁₀) j₀ a'₉))) (VectorsAVec.len a'₂) (i₀ + 1) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀)))
                 ) ∧
                (∀ (a'₁₁ : (VectorsAVec Int)),
                 ∀ (i₁ : Int),
                  ((k3 a'₂ i₀ j₀ old₀ lo₀ hi₀ (VectorsAVec.elems a'₁₁) (VectorsAVec.len a'₁₁) i₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ (VectorsAVec.elems a'₂) (VectorsAVec.len a'₂) i₀)) ->
                   ((k1 (j₀ + 1) (VectorsAVec.elems a'₁₁) (VectorsAVec.len a'₁₁) i₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)))
                )
               )
              )
          )
         
end F
