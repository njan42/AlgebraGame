import Game.Levels.PowMonoid.L04_PowMul

World "Monoid Power"
Level 5

Title "Powers of the Identity"

namespace MyAlgebra

Introduction "
What happens when every factor in a power is the identity?
Prove that `1 ^ n = 1` for every natural number `n`.
"

/-- `mpow_id n` states `(1 : M) ^ n = 1`. -/
TheoremDoc MyAlgebra.mpow_id as "mpow_id" in "Monoid Power"
Statement mpow_id {M : Type} [Monoid M] (n : ℕ) : (1 : M) ^ n = 1 := by
  induction n with
  | zero => rw [mpow_zero]
  | succ n ih => rw [mpow_succ_right, ih, mul_one]

Conclusion "Congrats!"

end MyAlgebra
