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
def k1 (a'₁₃ : Int) (a'₁₄ : Int) (a'₁₅ : (Arr Int)) (a'₁₆ : Int) (a'₁₇ : (Arr Int)) (a'₁₈ : Int) (a'₁₉ : Int) (a'₂₀ : Int) : Prop :=
  ((a'₁₃ ≥ 0) ∧ (a'₁₃ ≥ a'₁₄) ∧ (a'₁₃ ≥ a'₁₉) ∧ (a'₁₃ < a'₁₈) ∧ (a'₁₃ ≤ a'₁₈) ∧ (a'₁₃ ≤ a'₂₀) ∧ (a'₁₃ ≤ (a'₁₈ - 1)))
-- acyclic (non-cut) kvars
def k3 (i₀ : Int) (a'₃ : (VectorsAVec Int)) (j₀ : Int) (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (a'₂₁ : Int) (a'₂₂ : (Arr Int)) (a'₂₃ : Int) (a'₂₄ : (Arr Int)) (a'₂₅ : Int) (a'₂₆ : Int) (a'₂₇ : Int) (a'₂₈ : Int) (a'₂₉ : Int) (a'₃₀ : (Arr Int)) (a'₃₁ : Int) : Prop :=
  (((a'₂₁ = (i₀ + 1)) ∧ (a'₂₂ = (let a'₉ := ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₃))) : ((Int -> Int))) i₀); (let a'₁₀ := ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₃))) : ((Int -> Int))) j₀); (((((((((vectors_arr_set) : (((Arr Int) -> (Int -> (Int -> (Arr Int)))))) (((((((((vectors_arr_set) : (((Arr Int) -> (Int -> (Int -> (Arr Int)))))) (VectorsAVec.elems a'₃))) : ((Int -> (Int -> (Arr Int))))) i₀)) : ((Int -> (Arr Int)))) a'₁₀))) : ((Int -> (Int -> (Arr Int))))) j₀)) : ((Int -> (Arr Int)))) a'₉)))) ∧ (a'₃₁ = (VectorsAVec.len a'₃)) ∧ (a'₂₃ = (VectorsAVec.len a'₃)) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = lo₀) ∧ (a'₂₇ = hi₀) ∧ (a'₂₈ = j₀) ∧ (a'₂₉ = i₀) ∧ (a'₃₀ = (VectorsAVec.elems a'₃)) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len a'₃) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀)) ∧ (((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₃))) : ((Int -> Int))) j₀) ≤ ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) hi₀))) ∨ ((¬(((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems a'₃))) : ((Int -> Int))) j₀) ≤ ((((((vectors_arr_get) : (((Arr Int) -> (Int -> Int)))) (VectorsAVec.elems old₀))) : ((Int -> Int))) hi₀))) ∧ (a'₂₁ = i₀) ∧ (a'₂₂ = (VectorsAVec.elems a'₃)) ∧ (a'₃₁ = (VectorsAVec.len a'₃)) ∧ (a'₂₃ = (VectorsAVec.len a'₃)) ∧ (a'₂₄ = (VectorsAVec.elems old₀)) ∧ (a'₂₅ = (VectorsAVec.len old₀)) ∧ (a'₂₆ = lo₀) ∧ (a'₂₇ = hi₀) ∧ (a'₂₈ = j₀) ∧ (a'₂₉ = i₀) ∧ (a'₃₀ = (VectorsAVec.elems a'₃)) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀))))
def k0 (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (a'₃₂ : Int) (a'₃₃ : (Arr Int)) (a'₃₄ : Int) (a'₃₅ : Int) (a'₃₆ : Int) : Prop :=
  ((a'₃₃ = (VectorsAVec.elems old₀)) ∧ (a'₃₄ = (VectorsAVec.len old₀)) ∧ (a'₃₅ = lo₀) ∧ (a'₃₆ = hi₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)))
def k2 (old₀ : (VectorsAVec Int)) (lo₀ : Int) (hi₀ : Int) (j₀ : Int) (i₀ : Int) (a'₃ : (VectorsAVec Int)) (a'₃₇ : Int) (a'₃₈ : (Arr Int)) (a'₃₉ : Int) (a'₄₀ : Int) (a'₄₁ : Int) (a'₄₂ : Int) (a'₄₃ : Int) (a'₄₄ : (Arr Int)) (a'₄₅ : Int) : Prop :=
  ((a'₃₈ = (VectorsAVec.elems old₀)) ∧ (a'₃₉ = (VectorsAVec.len old₀)) ∧ (a'₄₀ = lo₀) ∧ (a'₄₁ = hi₀) ∧ (a'₄₂ = j₀) ∧ (a'₄₃ = i₀) ∧ (a'₄₄ = (VectorsAVec.elems a'₃)) ∧ (a'₄₅ = (VectorsAVec.len a'₃)) ∧ (j₀ ≥ 0) ∧ (j₀ ≥ i₀) ∧ (j₀ ≥ lo₀) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (j₀ < hi₀) ∧ (j₀ < (VectorsAVec.len old₀)) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (j₀ ≤ hi₀) ∧ (j₀ ≤ ((VectorsAVec.len old₀) - 1)) ∧ (j₀ ≤ (VectorsAVec.len old₀)))

end SortPartitionKVarSolutions


open SortPartitionKVarSolutions




def SortPartition := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (VectorsAVec Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (VectorsAVec Int)) -> (a2 : Int) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : (Arr Int)) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : (Arr Int)) -> (a16 : Int) -> Prop, 
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
          (((k1 lo₀ lo₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀))) ∧
          (∀ (j₀ : Int),
           ∀ (i₀ : Int),
            ∀ (a'₃ : (VectorsAVec Int)),
             ((k1 j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)) ->
              ((¬(j₀ < hi₀)) ->
               ((i₀ < (VectorsAVec.len a'₃))) ∧
               ((hi₀ < (VectorsAVec.len a'₃))) ∧
               (((VectorsAVec.len a'₃) ≥ 0) ->
                (((VectorsAVec.len a'₃) = (VectorsAVec.len old₀))) ∧
                ((sort_is_partitioned_by (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₅) hi₀ a'₄))) lo₀ i₀ (hi₀ + 1) i₀)) ∧
                ((sort_is_perm (VectorsAVec.elems old₀) (let a'₆ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₇ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) hi₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₇) hi₀ a'₆))) lo₀ hi₀)) ∧
                ((lo₀ ≤ i₀)) ∧
                ((i₀ ≤ hi₀))
                )
               ) ∧
              ((j₀ < hi₀) ->
               ((j₀ < (VectorsAVec.len a'₃))) ∧
               (∀ (a'₈ : Int),
                ((k2 old₀ lo₀ hi₀ j₀ i₀ a'₃ a'₈ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
               (((k2 old₀ lo₀ hi₀ j₀ i₀ a'₃ (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀))) ->
                 ((k3 i₀ a'₃ j₀ old₀ lo₀ hi₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) hi₀)) ->
                 ((i₀ < (VectorsAVec.len a'₃))) ∧
                 ((j₀ < (VectorsAVec.len a'₃))) ∧
                 (((VectorsAVec.len a'₃) ≥ 0) ->
                  ((k3 i₀ a'₃ j₀ old₀ lo₀ hi₀ (i₀ + 1) (let a'₉ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) i₀); (let a'₁₀ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₃) j₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₃) i₀ a'₁₀) j₀ a'₉))) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                 ) ∧
                (∀ (i₁ : Int),
                 ∀ (a'₁₂ : (VectorsAVec Int)),
                  ((k3 i₀ a'₃ j₀ old₀ lo₀ hi₀ i₁ (VectorsAVec.elems a'₁₂) (VectorsAVec.len a'₁₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ j₀ i₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   ((k1 (j₀ + 1) i₁ (VectorsAVec.elems a'₁₂) (VectorsAVec.len a'₁₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀)))
                )
               )
              )
          )
         
end F
