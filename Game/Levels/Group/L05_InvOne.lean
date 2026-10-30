import Game.Levels.Group.L04_InvUnique

World "Group"
Level 5

Title "Inverse of the Identity"

namespace MyAlgebra

Introduction "
What is the inverse of the identity? Check its two inverse products.
"

/-- `inv_one` states `1⁻¹ = 1`, so rewriting simplifies the inverse of the identity. -/
TheoremDoc MyAlgebra.inv_one as "inv_one" in "Group"
@[to_additive neg_zero]
Statement inv_one {G} [Group G] : (1 : G)⁻¹ = 1 := by
  Hint "Which two products show that `1` is an inverse of itself?"
  have h : (1 : G) = (1 : G)⁻¹ := by
    apply inv_unique 1
    constructor
    · rw [mul_one]
    · rw [one_mul]
  rw [← h]

Conclusion "Congrats!"

end MyAlgebra
