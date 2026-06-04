import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.MemoFibMemo
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def MemoFibMemo_proof : MemoFibMemo := by
  unfold MemoFibMemo
  exists MemoFibMemoKVarSolutions.k0
  exists MemoFibMemoKVarSolutions.k1
  simp [MemoFibMemoKVarSolutions.k0, MemoFibMemoKVarSolutions.k1]
  zap

end F
