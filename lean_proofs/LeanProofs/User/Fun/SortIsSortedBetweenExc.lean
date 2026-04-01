import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr

namespace F

@[simp]
def sort_is_sorted_between_exc (a: Arr Int) (lo hi mid: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi /\ j != mid) -> (a i <= a j)


end F
