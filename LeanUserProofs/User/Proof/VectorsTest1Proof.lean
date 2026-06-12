import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VectorsTest1
-- import LeanProofs.Lib.Tactics
import LeanFixpoint
import LeanProofs.Lib.Lemmas

namespace F
open VectorsTest1KVarSolutions

def VectorsTest1_proof : VectorsTest1 := by
  unfold VectorsTest1
  fusion
  solve_fixpoint

end F
