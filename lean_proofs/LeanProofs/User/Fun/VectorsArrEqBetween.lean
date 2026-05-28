import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr
import LeanProofs.User.Struct.Arr
open Classical

namespace F

@[grind]
noncomputable def vectors_arr_eq_between : {t0 : Type} -> [Inhabited t0] -> (Arr t0) -> (Arr t0) -> Int -> Int -> Prop :=
  fun v1 v2 l r => ∀ i, l ≤ i ∧ i < r → v1 i = v2 i


end F
