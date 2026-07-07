import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def ringbuffer_fslice_get : {t0 : Type} -> [Inhabited t0] -> (FSlice t0) -> Int -> t0 :=
  fun s i => s[i.toNat]!


end F
