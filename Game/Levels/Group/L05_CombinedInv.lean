import Game.Levels.Group.L04_InvUnique

World "Group"
Level 5

Title "Inverse of a Product"

namespace MyAlgebra

Introduction "
What is the inverse of `g * h`?

Our group has inverses of elements by definition but what about the inverse
of the product of elements? Since products of elements are elements of the
group, they should have inverses too.

This exposes the anti-commutativity of the inverse operation.
"

/--
`inv_anticomm g h` states `h⁻¹ * g⁻¹ = (g * h)⁻¹`: taking inverses reverses the order of it's
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
