import Game.Levels.PowGroup.L01_PowNegNat

World "Group Power"
Level 2

Title "The Exponent Minus One"

namespace MyAlgebra

Introduction "
Show that raising a group element to the power `-1` gives its inverse.
"

/-- `gpow_neg_one g` states `g ^ (-1 : ℤ) = g⁻¹`. -/
TheoremDoc MyAlgebra.gpow_neg_one as "gpow_neg_one" in "Group Power"
Statement gpow_neg_one {G : Type} [Group G] (g : G) : g ^ (-1 : ℤ) = g⁻¹ := by
  Hint "What does the negative-natural-exponent law say when the natural exponent is `1`?"
  have h := gpow_neg_mpow g 1
  rw [mpow_one] at h
  exact h

Conclusion "Congrats!"

end MyAlgebra
