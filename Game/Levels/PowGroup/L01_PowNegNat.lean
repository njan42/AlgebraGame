import Game.MyAlgebra.PowGroup

World "Group Power"
Level 1

Title "Negative Natural Exponents"

namespace MyAlgebra

Introduction "
Integer powers extend natural powers by using inverses for negative exponents.
The notation `(n : ℤ)` treats a natural number as an integer.
`gpow_neg_nat` expresses the definition as `g ^ (-(n : ℤ)) = (g⁻¹) ^ n`.

Show that this is also the inverse of the natural power `g ^ n`.
"

/-- A negative natural exponent gives the inverse of the natural power. -/
TheoremDoc MyAlgebra.gpow_neg_mpow as "gpow_neg_mpow" in "Group Power"
Statement gpow_neg_mpow {G : Type} [Group G] (g : G) (n : ℕ) :
    g ^ (-(n : ℤ)) = (g ^ n)⁻¹ := by
  Hint "The negative-exponent rule gives a power of an inverse.
  Which rule relates that to the inverse of a power?"
  rw [gpow_neg_nat, ← inv_mpow]

/-- `gpow_zero g` states `g ^ (0 : ℤ) = 1`. -/
TheoremDoc MyAlgebra.gpow_zero as "gpow_zero" in "Group Power"
/-- `gpow_one g` states `g ^ (1 : ℤ) = g`. -/
TheoremDoc MyAlgebra.gpow_one as "gpow_one" in "Group Power"
/-- `gpow_succ g n` states `g ^ (n + 1) = g ^ n * g` for integer `n`. -/
TheoremDoc MyAlgebra.gpow_succ as "gpow_succ" in "Group Power"
/-- `gpow_neg_nat g n` states `g ^ (-(n : ℤ)) = (g⁻¹) ^ n`. -/
TheoremDoc MyAlgebra.gpow_neg_nat as "gpow_neg_nat" in "Group Power"
/-- `inv_mpow g n` states `(g ^ n)⁻¹ = (g⁻¹) ^ n` for natural `n`. -/
TheoremDoc MyAlgebra.inv_mpow as "inv_mpow" in "Group Power"
NewTheorem MyAlgebra.gpow_zero MyAlgebra.gpow_one MyAlgebra.gpow_succ
  MyAlgebra.gpow_neg_nat MyAlgebra.inv_mpow

Conclusion "Congrats!"

end MyAlgebra
