import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[simp, grind]
def my_min (a b : Int) : Int := if a < b then a else b

@[simp, grind]
noncomputable def ringbuffer_init_inv (num_enqueues len : Int) (init : SmtMap Int Prop) : Prop :=
  ∀ idx, (0 <= idx ∧ idx < my_min num_enqueues len) → SmtMap_select init idx


end F
