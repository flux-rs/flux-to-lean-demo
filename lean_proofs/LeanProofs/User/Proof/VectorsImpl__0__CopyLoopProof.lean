import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.VectorsImpl__0__CopyLoop
import LeanProofs.Lib.Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def VectorsImpl__0__CopyLoop_proof : VectorsImpl__0__CopyLoop := by
  unfold VectorsImpl__0__CopyLoop
  simp_all [vectors_arr_eq_between, vectors_arr_get, vectors_arr_set]
  zapt

end F
