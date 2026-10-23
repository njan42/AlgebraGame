import Game.Levels.PowMonoid.L01_PowOne

World "Monoid Power"
Level 2

Title "Multiplying on the Left"

namespace MyAlgebra

Introduction "
The definition adds a factor on the right. Can we put that factor on the left instead?
Prove the statement by induction on the exponent.
"

/-- `mpow_succ_left m n` states `m ^ (n + 1) = m * m ^ n`. -/
TheoremDoc MyAlgebra.mpow_succ_left as "mpow_succ_left" in "Monoid Power"
Statement mpow_succ_left {M : Type} [Monoid M] (m : M) (n : ℕ) :
    m ^ (n + 1) = m * m ^ n := by
  induction n with
  | zero => rw [mpow_one, mpow_zero, mul_one]
  | succ n ih =>
    Hint "Expand one factor at a time in a `calc` block, using `{ih}` in the middle."
    calc
      m ^ ((n + 1) + 1) = m ^ (n + 1) * m := mpow_succ_right m
      _ = (m * m ^ n) * m := by rw [ih]
      _ = m * (m ^ n * m) := mul_assoc m (m ^ n) m
      _ = m * m ^ (n + 1) := by rw [mpow_succ_right]


Conclusion "Congrats! This uses associativity, without assuming that multiplication is commutative."

end MyAlgebra
