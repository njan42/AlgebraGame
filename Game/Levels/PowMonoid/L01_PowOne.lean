import Game.Levels.Monoid
import Game.MyAlgebra.PowMonoid

World "Monoid Power"
Level 1

Title "First Power"

namespace MyAlgebra

Introduction "
We defined natural powers by `m ^ 0 = 1` and `m ^ (n + 1) = m ^ n * m`.
In this level, prove that the first power of an element is the element itself.
"

/-- `mpow_one m` states `m ^ 1 = m`. -/
TheoremDoc MyAlgebra.mpow_one as "mpow_one" in "Monoid Power"
Statement mpow_one {M : Type} [Monoid M] (m : M) : m ^ 1 = m := by
  Hint "How does exponent `1` fit the successor rule?"
  rw [mpow_succ_right, mpow_zero, one_mul]

/-- `mpow_zero m` states `m ^ 0 = 1`. -/
TheoremDoc MyAlgebra.mpow_zero as "mpow_zero" in "Monoid Power"
/-- `mpow_succ_right m` states `m ^ (n + 1) = m ^ n * m`. -/
TheoremDoc MyAlgebra.mpow_succ_right as "mpow_succ_right" in "Monoid Power"
/-- Induction on a natural number has a `zero` case and a `succ n ih` case. -/
TacticDoc induction
NewTactic induction
NewTheorem MyAlgebra.mpow_zero MyAlgebra.mpow_succ_right

Conclusion "Congrats!"

end MyAlgebra
