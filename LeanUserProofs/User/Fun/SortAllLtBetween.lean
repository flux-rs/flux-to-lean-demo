import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr

namespace F

@[simp]
def sort_all_lt_between (a: Arr Int) (lo hi x: Int) : Prop :=
  forall i, (lo <= i /\ i < hi) -> a i < x

end F
