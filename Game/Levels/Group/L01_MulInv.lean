import Game.Levels.Monoid.L03_OneUnique

World "Group"
Level 1

Title "Right Multiplicative Inverse"

namespace MyAlgebra

Introduction "Starting with the left inverse law `g⁻¹ * g = 1`, prove the right inverse law `g * g⁻¹ = 1`. Use associativity and the identity laws. This prepares us to prove cancellation."

/--
`mul_inv` is a proof that for all `g : G`, `g * g⁻¹ = 1` (Right Inverse Axiom).
-/
TheoremDoc MyAlgebra.mul_inv' as "mul_inv" in "Group"
Statement mul_inv' {G} (g : G) [Group G] : g * g⁻¹ = 1 := by
  Hint "We have a similar lemma for the left inverse, can we use it here?"
  rw [←one_mul (g * _)]
  rw [←inv_mul (g⁻¹)]
  rw [mul_assoc]
  rw [←mul_assoc (g⁻¹)]
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats!"

/--
`mul_inv` is a proof that for all `g : G`, `g * g⁻¹ = 1` (Right Inverse Axiom).
-/
TheoremDoc MyAlgebra.Group.mul_inv as "mul_inv" in "Group"

/-- `inv_mul g` states `g⁻¹ * g = 1` (left inverse). -/
TheoremDoc MyAlgebra.Group.inv_mul as "inv_mul" in "Group"

NewTheorem MyAlgebra.Group.inv_mul
