import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibPtrTest
open Classical
set_option linter.unusedVariables false


namespace F

def FibPtrTest_proof : FibPtrTest := by
  unfold FibPtrTest
  grind

end F
