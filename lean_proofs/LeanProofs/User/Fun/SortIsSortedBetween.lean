import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanFixpoint

namespace F

@[simp]
def sort_is_sorted_between (a: Arr Int) (lo hi: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi) -> (a i <= a j)

end F
