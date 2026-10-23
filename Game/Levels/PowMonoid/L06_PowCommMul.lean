import Game.Levels.PowMonoid.L05_PowId

World "Monoid Power"
Level 6

Title "Commuting a Power with Its Base"

namespace MyAlgebra

Introduction "
An element may not necessarily commute with every element of a monoid.
Does it commute with its own powers? Compare the two rules for `m ^ (n + 1)`.
"

/-- A power commutes with its base: `m ^ n * m = m * m ^ n`. -/
TheoremDoc MyAlgebra.mpow_comm_mul as "mpow_comm_mul" in "Monoid Power"
Statement mpow_comm_mul {M : Type} [Monoid M] (m : M) (n : ℕ) : m ^ n * m = m * m ^ n := by
  rw [← mpow_succ_right, mpow_succ_left]

Conclusion "Congrats!"

end MyAlgebra
