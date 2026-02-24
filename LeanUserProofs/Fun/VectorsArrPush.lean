import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr

namespace F

@[grind]
def vectors_arr_push : {t0 : Type} -> [Inhabited t0] -> (Array t0) -> t0 -> (Array t0) := Array.push


end F
