import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Main
open Classical
set_option linter.unusedVariables false


namespace F

def Main_proof : Main := by
  unfold Main
  grind

end F
