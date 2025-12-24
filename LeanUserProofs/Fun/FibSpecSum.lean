import LeanProofs.Flux.Prelude
def fib_spec_sum (n : Int) : Int :=
  if n <= 0 then 0 else  n + fib_spec_sum ( n - 1)
  termination_by n.toNat
