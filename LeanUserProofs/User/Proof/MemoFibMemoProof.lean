import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.MemoFibMemo
-- import LeanProofs.Lib.Tactics
import Flex
open Classical
set_option linter.unusedVariables false


namespace F

def MemoFibMemo_proof : MemoFibMemo := by
  unfold MemoFibMemo
  solve_fixpoint

end F
