import LeanProofs.Flux.Prelude
open Classical

namespace F

namespace FibSqrtKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₁ : Int) (a'₂ : Int) : Prop :=
  (a'₁ ≥ 0)

end FibSqrtKVarSolutions


open FibSqrtKVarSolutions




def FibSqrt := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ ≠ 0) ->
    (((k0 0 x₀))) ∧
    (∀ (i₀ : Int),
     ((k0 i₀ x₀)) ->
      ((¬((i₀ * i₀) ≤ x₀)) ->
       (((i₀ - 1) ≥ 0)) ∧
       (((((i₀ - 1) * (i₀ - 1)) ≤ x₀)) ∧
       ((x₀ < (((i₀ - 1) + 1) * ((i₀ - 1) + 1))))
       )
       ) ∧
      (((i₀ * i₀) ≤ x₀) ->
       ((k0 (i₀ + 1) x₀)))
      )
    ) ∧
   ((¬(x₀ ≠ 0)) ->
    (((0 * 0) ≤ x₀)) ∧
    ((x₀ < ((0 + 1) * (0 + 1))))
    )
   
end F
