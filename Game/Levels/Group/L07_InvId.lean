import Game.Levels.Group.L06_CombinedInv2

World "Group"
Level 7

Title "Inverse of the Identity"

namespace MyAlgebra

Introduction "
What is the inverse of the identity? Check its two inverse products.
"

/--
`inv_id` states `1 = 1⁻¹`. Use it backwards to simplify the inverse of `1`.
-/
TheoremDoc MyAlgebra.inv_id as "inv_id" in "Group"
Statement inv_id {G} [Group G] : (1 : G) = (1 : G)⁻¹ := by
  apply inv_unique 1

  constructor
  rw [mul_one]
  rw [one_mul]

Conclusion "Congrats!"

end MyAlgebra
