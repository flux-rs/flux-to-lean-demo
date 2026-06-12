import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortTest2
import LeanProofs.Lib.Tactics
import LeanProofs.Lib.Lemmas

namespace F

def SortTest2_proof : SortTest2 := by
  unfold SortTest2
  simp_all [sort_is_sorted_between]
  zapNamed


end F
