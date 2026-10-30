import Game.Levels.Group.L05_InvOne

World "Group"
Level 6

Title "Inverse of a Product"

namespace MyAlgebra

Introduction "
What is the inverse of `g * h`? It uses the inverses of both factors,
but in which order?
"

/--
`inv_anticomm g h` states `h⁻¹ * g⁻¹ = (g * h)⁻¹`: taking inverses reverses the order of its
factors.
-/
TheoremDoc MyAlgebra.inv_anticomm as "inv_anticomm" in "Group"
Statement inv_anticomm {G} (g h : G) [Group G] : (h⁻¹ * g⁻¹) = (g * h)⁻¹ := by
  Hint "What two products must you check to identify an inverse using `inv_unique`?"
  apply inv_unique (g * h) (h⁻¹ * g⁻¹)
  constructor
  · rw [← mul_assoc, mul_assoc g h h⁻¹, mul_inv, mul_one, mul_inv]
  · rw [← mul_assoc, mul_assoc h⁻¹ g⁻¹ g, inv_mul, mul_one, inv_mul]

Conclusion "Congrats!"

end MyAlgebra
