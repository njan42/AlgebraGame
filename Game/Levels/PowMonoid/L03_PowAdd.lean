import Game.Levels.PowMonoid.L02_PowSuccLeft

World "Monoid Power"
Level 3

Title "Adding Exponents"

namespace MyAlgebra

Introduction "
Prove the addition law for natural exponents.
What happens when one more factor is added to the second power?
"

/-- `mpow_add m x y` states `m ^ (x + y) = m ^ x * m ^ y`. -/
TheoremDoc MyAlgebra.mpow_add as "mpow_add" in "Monoid Power"
Statement mpow_add {M : Type} [Monoid M] (m : M) (x y : ℕ) :
    m ^ (x + y) = m ^ x * m ^ y := by
  induction y with
  | zero =>
    Hint "`Nat.add_zero x` simplifies `x + 0`."
    rw [Nat.add_zero, mpow_zero, mul_one]
  | succ y ih =>
    Hint "`Nat.add_succ x y` rewrites `x + (y + 1)` as `(x + y) + 1`."
    rw [Nat.add_succ, mpow_succ_right, ih, mpow_succ_right, mul_assoc]

/-- `Nat.add_zero n` states `n + 0 = n`. -/
TheoremDoc Nat.add_zero as "Nat.add_zero" in "Nat"
/-- `Nat.add_succ x y` states `x + (y + 1) = (x + y) + 1`. -/
TheoremDoc Nat.add_succ as "Nat.add_succ" in "Nat"
NewTheorem Nat.add_zero Nat.add_succ

Conclusion "Congrats!"

end MyAlgebra
