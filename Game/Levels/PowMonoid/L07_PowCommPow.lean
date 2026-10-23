import Game.Levels.PowMonoid.L06_PowCommMul

World "Monoid Power"
Level 7

Title "Powers of One Element Commute"

namespace MyAlgebra

Introduction "
We know that `m` commutes with its own powers.
Show that any two powers of this same element commute with each other.
"

/-- Powers of the same element commute with each other. -/
TheoremDoc MyAlgebra.mpow_comm_mpow as "mpow_comm_mpow" in "Monoid Power"
Statement mpow_comm_mpow {M : Type} [Monoid M] (m : M) (x y : ℕ) :
    m ^ x * m ^ y = m ^ y * m ^ x := by
  Hint "What happens to the exponents when powers of the same element are multiplied?
  `Nat.add_comm x y` exchanges `x + y` and `y + x`."
  rw [← mpow_add, ← mpow_add, Nat.add_comm]

/-- `Nat.add_comm x y` states `x + y = y + x`. -/
TheoremDoc Nat.add_comm as "Nat.add_comm" in "Nat"
NewTheorem Nat.add_comm


Conclusion "Congrats! Powers of one element commute, even in a noncommutative monoid."

end MyAlgebra
