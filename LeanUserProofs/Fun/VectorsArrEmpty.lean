import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr

namespace F

@[grind]
def vectors_arr_empty : {t0 : Type} -> [Inhabited t0] -> (Array t0) := Array.empty


end F
