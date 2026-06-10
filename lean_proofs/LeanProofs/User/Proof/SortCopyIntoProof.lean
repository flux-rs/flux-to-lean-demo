import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortCopyInto
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def SortCopyInto_proof : SortCopyInto := by
  unfold SortCopyInto
  zapt

end F
