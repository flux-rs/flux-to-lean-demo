import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.FibNinety
import LeanFixpoint

namespace F

def FibNinety_proof : FibNinety := by
  solve_fixpoint

end F
