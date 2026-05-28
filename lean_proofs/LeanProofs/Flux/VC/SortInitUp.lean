import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.SortIsSortedBetween
import LeanProofs.User.Fun.VectorsArrSet
open Classical

namespace F

namespace SortInitUpKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₂ : (Arr Int)) (a'₃ : Int) (a'₄ : Int) (a'₅ : (Arr Int)) (a'₆ : Int) : Prop :=
  True

end SortInitUpKVarSolutions


open SortInitUpKVarSolutions




def SortInitUp := ∃ k0 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ((VectorsAVec.len old₀) ≥ 0) ->
   (((k0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) 0 (VectorsAVec.elems old₀) (VectorsAVec.len old₀)))) ∧
   (∀ (a'₀ : (VectorsAVec Int)),
    ∀ (i₀ : Int),
     ((k0 (VectorsAVec.elems a'₀) (VectorsAVec.len a'₀) i₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀))) ->
      ((¬(i₀ < (VectorsAVec.len old₀))) ->
       (sort_is_sorted_between (VectorsAVec.elems a'₀) 0 (VectorsAVec.len a'₀))) ∧
      ((i₀ < (VectorsAVec.len old₀)) ->
       ((i₀ < (VectorsAVec.len a'₀))) ∧
       (((VectorsAVec.len a'₀) ≥ 0) ->
        ((k0 (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₀) i₀ i₀) (VectorsAVec.len a'₀) (i₀ + 1) (VectorsAVec.elems old₀) (VectorsAVec.len old₀))))
       )
      )
   
end F
