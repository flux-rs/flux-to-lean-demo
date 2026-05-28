import LeanProofs.Flux.Prelude
import LeanProofs.User.Fun.FibSpecSum
open Classical

namespace F

namespace FibSumLoopKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₂ : Int) (a'₃ : Int) (a'₄ : Int) : Prop :=
  ((a'₂ ≥ 0) ∧ (a'₂ ≤ a'₃) ∧ (a'₂ ≤ a'₄))

end FibSumLoopKVarSolutions


open FibSumLoopKVarSolutions




def FibSumLoop := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((k0 0 0 n₀))) ∧
   (∀ (i₀ : Int),
    ∀ (total₀ : Int),
     ((k0 i₀ total₀ n₀)) ->
      ((¬(i₀ < n₀)) ->
       (total₀ = (fib_spec_sum n₀))) ∧
      ((i₀ < n₀) ->
       ((k0 (i₀ + 1) (total₀ + (i₀ + 1)) n₀)))
      )
   
end F
