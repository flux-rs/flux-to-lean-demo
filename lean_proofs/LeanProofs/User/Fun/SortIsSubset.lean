import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.User.Struct.Arr
open Classical
set_option linter.unusedVariables false


namespace F

noncomputable def sort_is_subset (arr: Arr Int) (lo: Int) (hi: Int) (arr': Arr Int) (lo': Int) (hi': Int) : Prop :=
  ∀ i, lo ≤ i ∧ i < hi → ∃ j, lo' ≤ j ∧ j < hi' ∧ arr i = arr' j

end F
