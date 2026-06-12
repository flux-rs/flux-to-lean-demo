import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.MemoTestMemo
open Classical
set_option linter.unusedVariables false


namespace F

def MemoTestMemo_proof : MemoTestMemo := by
  unfold MemoTestMemo
  grind

end F
