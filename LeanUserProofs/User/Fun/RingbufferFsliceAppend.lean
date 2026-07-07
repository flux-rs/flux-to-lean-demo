import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.User.Struct.FSlice
import LeanProofs.User.Struct.FSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def ringbuffer_fslice_append : {t0 : Type} -> [Inhabited t0] -> (FSlice t0) -> (FSlice t0) -> (FSlice t0) :=
  fun s1 s2 => s1 ++ s2


end F
