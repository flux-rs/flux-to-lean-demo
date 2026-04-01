import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
open Classical

namespace F

@[simp]
noncomputable def sort_is_partitioned_by (arr: Arr Int) (lo mid hi pivot: Int) : Prop :=
  (forall ix, (lo <= ix /\ ix < mid) -> (arr ix <= arr pivot)) /\
  (forall ix, (mid <= ix /\ ix < hi) -> (arr pivot <= arr ix))


end F
