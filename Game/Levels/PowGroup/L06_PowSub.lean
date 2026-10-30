import Game.Levels.PowGroup.L05_PowNeg

World "Group Power"
Level 6

Title "Subtracting Integer Exponents"

namespace MyAlgebra

Introduction "
Subtraction of exponents corresponds to multiplying by an inverse.
Combine the addition and negation laws to prove the subtraction law.
"

/-- `gpow_sub g x y` states `g ^ x * (g ^ y)⁻¹ = g ^ (x - y)`. -/
TheoremDoc MyAlgebra.gpow_sub as "gpow_sub" in "Group Power"
Statement gpow_sub {G : Type} [Group G] (g : G) (x y : ℤ) :
    g ^ x * (g ^ y)⁻¹ = g ^ (x - y) := by
  Hint "`Int.sub_eq_add_neg x y` writes `x - y` as `x + (-y)`."
  rw [Int.sub_eq_add_neg, ← gpow_add, gpow_neg]

/-- `Int.sub_eq_add_neg a b` states `a - b = a + (-b)`. -/
TheoremDoc Int.sub_eq_add_neg as "Int.sub_eq_add_neg" in "Int"
NewTheorem Int.sub_eq_add_neg

Conclusion "Congrats!"

end MyAlgebra
