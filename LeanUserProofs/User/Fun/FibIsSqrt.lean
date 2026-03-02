import LeanProofs.Flux.Prelude

namespace F

@[grind]
def fib_is_sqrt (res: Int) (x: Int) : Prop :=
  res * res <= x /\ x < (res + 1) * (res + 1)

end F
