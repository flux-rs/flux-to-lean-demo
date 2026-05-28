import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F

namespace SortTestSortedKVarSolutions

-- acyclic (non-cut) kvars
def k0 (me₀ : (VectorsAVec Int)) (a'₂ : Int) (a'₃ : (Arr Int)) (a'₄ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems me₀))) : ((Int -> (Int -> Prop)))) 0)) : ((Int -> Prop))) (VectorsAVec.len me₀)) ∧ (a'₃ = (VectorsAVec.elems me₀)) ∧ (a'₄ = (VectorsAVec.len me₀)) ∧ ((VectorsAVec.len me₀) ≥ 0) ∧ (100 < (VectorsAVec.len me₀)))
def k1 (me₀ : (VectorsAVec Int)) (a'₅ : Int) (a'₆ : (Arr Int)) (a'₇ : Int) : Prop :=
  ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems me₀))) : ((Int -> (Int -> Prop)))) 0)) : ((Int -> Prop))) (VectorsAVec.len me₀)) ∧ (a'₆ = (VectorsAVec.elems me₀)) ∧ (a'₇ = (VectorsAVec.len me₀)) ∧ ((VectorsAVec.len me₀) ≥ 0) ∧ (100 < (VectorsAVec.len me₀)))

end SortTestSortedKVarSolutions


open SortTestSortedKVarSolutions




def SortTestSorted := ∃ k0 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> Prop, ∃ k1 : (a0 : (VectorsAVec Int)) -> (a1 : Int) -> (a2 : (Arr Int)) -> (a3 : Int) -> Prop, 
 ∀ (me₀ : (VectorsAVec Int)),
  ((VectorsAVec.len me₀) ≥ 0) ->
   ((sort_is_sorted_between (VectorsAVec.elems me₀) 0 (VectorsAVec.len me₀)) ∧ (100 < (VectorsAVec.len me₀))) ->
    ((0 < (VectorsAVec.len me₀))) ∧
    (∀ (a'₀ : Int),
     ((k0 me₀ a'₀ (VectorsAVec.elems me₀) (VectorsAVec.len me₀)))) ∧
    (((k0 me₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 0) (VectorsAVec.elems me₀) (VectorsAVec.len me₀))) ->
     ((1 < (VectorsAVec.len me₀))) ∧
     (∀ (a'₁ : Int),
      ((k1 me₀ a'₁ (VectorsAVec.elems me₀) (VectorsAVec.len me₀)))) ∧
     (((k1 me₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 1) (VectorsAVec.elems me₀) (VectorsAVec.len me₀))) ->
      (((vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 0) ≤ (vectors_arr_get (t0 := Int) (VectorsAVec.elems me₀) 1)) = True))
     )
    
end F
