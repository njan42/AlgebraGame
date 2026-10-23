import Game.Levels.Monoid

World "Group"
Level 1

Title "Right Multiplicative Inverse"

namespace MyAlgebra

Introduction "
A group has inverses as well as the monoid laws. Starting with the left inverse
law `g⁻¹ * g = 1`, show that `g * g⁻¹ = 1` too.
The right inverse law will become available after this level.

An inverse is also a group element, so the left inverse law applies to it too.
We will use associativity to bring an element and its left inverse together.
"

set_option linter.unusedTactic false in
Statement {G} (g : G) [Group G] : g * g⁻¹ = 1 := by
  Hint "Could inserting an identity on the left help us use the left inverse law?"
  rw [←one_mul (g * g⁻¹)]
  Hint "What does the left inverse law say when the element is `{g}⁻¹`?
  Use that equality to replace the `1` on the left."
  rw [←inv_mul (g⁻¹)]
  Hint "The factors are in the right order. How can you regroup them to simplify
  the product `{g}⁻¹ * {g}`?"
  rw [mul_assoc]
  Hint "Inside the outer product, group the first two factors together."
  rw [←mul_assoc (g⁻¹)]
  Hint "Simplify the inner inverse product and the identity it leaves behind."
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats! The right inverse law `mul_inv` is now available."

/-- `mul_inv g` states `g * g⁻¹ = 1` (right inverse). -/
TheoremDoc MyAlgebra.Group.mul_inv as "mul_inv" in "Group"

/-- `inv_mul g` states `g⁻¹ * g = 1` (left inverse). -/
TheoremDoc MyAlgebra.Group.inv_mul as "inv_mul" in "Group"

NewTheorem MyAlgebra.Group.inv_mul

end MyAlgebra
