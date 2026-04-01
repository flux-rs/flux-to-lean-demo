import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FibBozo
open Classical

namespace F



def FibTestBozo := 
 ∀ (b₀ : FibBozo),
  ((FibBozo.x b₀) ≥ 0) ->
   (¬(FibBozo.y b₀)) ->
    (((FibBozo.x b₀) + 20) = (if (FibBozo.y b₀) then ((FibBozo.x b₀) + 10) else ((FibBozo.x b₀) + 20)))
end F
