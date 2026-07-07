import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.FSlice
import LeanProofs.User.Struct.FSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
noncomputable def ringbuffer_fslice_subslice : {t0 : Type} -> [Inhabited t0] -> (FSlice t0) -> Int -> Int -> (FSlice t0) :=
  fun s l r => (s.drop l.toNat).take (r.toNat - l.toNat)


end F
