import LeanProofs.Flux.Prelude
import LeanProofs.User.Struct.Arr

namespace F

@[grind]
def vectors_arr_get [Inhabited t0] (arr: Arr t0)(idx: Int) : t0  := arr[idx.toNat]!


end F
