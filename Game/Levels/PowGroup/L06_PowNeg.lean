import Game.Levels.PowGroup.L05_PowAdd

World "Group Power"
Level 6

Title "Negating an Exponent"

namespace MyAlgebra

Introduction "
We now have the addition law for arbitrary integers.
What happens when the two exponents add to zero?
Use the inverse uniqueness result to identify the power with exponent `-n`.
"

/-- `gpow_neg g n` states `g ^ (-n) = (g ^ n)⁻¹`. -/
TheoremDoc MyAlgebra.gpow_neg as "gpow_neg" in "Group Power"
Statement gpow_neg {G : Type} [Group G] (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  apply inv_unique (g ^ n)
  constructor
  · Hint "`Int.add_right_neg n` states `n + (-n) = 0`."
    rw [gpow_add, Int.add_right_neg, gpow_zero]
  · Hint "`Int.add_left_neg n` states `-n + n = 0`."
    rw [gpow_add, Int.add_left_neg, gpow_zero]

/-- `Int.add_right_neg n` states `n + (-n) = 0`. -/
TheoremDoc Int.add_right_neg as "Int.add_right_neg" in "Int"
/-- `Int.add_left_neg n` states `-n + n = 0`. -/
TheoremDoc Int.add_left_neg as "Int.add_left_neg" in "Int"
NewTheorem Int.add_right_neg Int.add_left_neg

Conclusion "Congrats!"

end MyAlgebra
