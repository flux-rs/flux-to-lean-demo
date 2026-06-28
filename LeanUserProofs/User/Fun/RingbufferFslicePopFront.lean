import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.User.Struct.FSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def ringbuffer_fslice_pop_front : {t0 : Type} -> [Inhabited t0] -> (FSlice t0) -> (FSlice t0) :=
  fun s => s.drop 1


end F
