import Game.Levels.PowMonoid.L03_PowAdd

World "Monoid Power"
Level 4

Title "Multiplying Exponents"

namespace MyAlgebra

Introduction "
A power of a power repeats a block of factors.
Show that taking the `y`th power of `m ^ x` gives `m ^ (x * y)`.
"

/-- `mpow_mul m x y` states `m ^ (x * y) = (m ^ x) ^ y`. -/
TheoremDoc MyAlgebra.mpow_mul as "mpow_mul" in "Monoid Power"
Statement mpow_mul {M : Type} [Monoid M] (m : M) (x y : ℕ) :
    m ^ (x * y) = (m ^ x) ^ y := by
  induction y with
  | zero =>
    Hint "`Nat.mul_zero x` simplifies `x * 0`."
    rw [Nat.mul_zero, mpow_zero, mpow_zero]
  | succ y ih =>
    Hint "`Nat.mul_succ x y` rewrites `x * (y + 1)` as `x * y + x`.
    Then use the addition law for powers."
    rw [Nat.mul_succ, mpow_add, ih, mpow_succ_right]

/-- `Nat.mul_zero n` states `n * 0 = 0`. -/
TheoremDoc Nat.mul_zero as "Nat.mul_zero" in "Nat"
/-- `Nat.mul_succ x y` states `x * (y + 1) = x * y + x`. -/
TheoremDoc Nat.mul_succ as "Nat.mul_succ" in "Nat"
NewTheorem Nat.mul_zero Nat.mul_succ

Conclusion "Congrats!"

end MyAlgebra
