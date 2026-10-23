import Game.Levels.PowGroup.L02_PowNegOne

World "Group Power"
Level 3

Title "Two Integer Steps"

namespace MyAlgebra

Introduction "
The rule `gpow_succ` works for every integer, including negative exponents.
Use it to describe what happens when the exponent increases by two.
"

/-- `g ^ ((n + 1) + 1) = (g ^ n * g) * g` for every integer `n`. -/
TheoremDoc MyAlgebra.gpow_two_steps as "gpow_two_steps" in "Group Power"
Statement gpow_two_steps {G : Type} [Group G] (g : G) (n : ℤ) :
    g ^ ((n + 1) + 1) = (g ^ n * g) * g := by
  Hint "How much does each use of the successor rule change the exponent?"
  rw [gpow_succ, gpow_succ]

Conclusion "Congrats!"

end MyAlgebra
