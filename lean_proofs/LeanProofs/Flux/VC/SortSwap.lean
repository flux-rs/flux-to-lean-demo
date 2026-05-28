import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.Flux.Struct.VectorsAVec
import LeanProofs.User.Fun.VectorsArrSet
import LeanProofs.User.Fun.VectorsArrGet
open Classical

namespace F



def SortSwap := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (src₀ : Int),
   ∀ (dst₀ : Int),
    (src₀ < (VectorsAVec.len old₀)) ->
     (dst₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (src₀ ≥ 0) ->
        (dst₀ ≥ 0) ->
         (∀ (a'₀ : Int),
          ((k0 a'₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) src₀ dst₀))) ∧
         (((k0 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) src₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) src₀ dst₀)) ->
          (∀ (a'₁ : Int),
           ((k1 a'₁ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) src₀ dst₀))) ∧
          (((k1 (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) dst₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) src₀ dst₀)) ->
           ((vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems old₀) src₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) dst₀)) dst₀ (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) src₀)) = (let a'₂ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) src₀); (let a'₃ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems old₀) dst₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems old₀) src₀ a'₃) dst₀ a'₂)))))
          )
         
end F
