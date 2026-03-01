import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VectorsTest1
import LeanProofs.Lib.Tactics

namespace F
open VectorsTest1KVarSolutions

def VectorsTest1_proof : VectorsTest1 := by
  unfold VectorsTest1
  exists k0; exists k1; exists k2; exists k3
  simp [k0, k1, k2, k3]
  zap


end F
