import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.NestedGenericTest
open Classical
set_option linter.unusedVariables false


namespace F

def NestedGenericTest_proof : NestedGenericTest := by
  unfold NestedGenericTest
  intro x h1 h2; omega

end F
