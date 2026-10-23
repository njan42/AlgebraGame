import Game.Levels.Group.L07_InvId

World "Group"
Level 8

Title "Inverse of an Inverse"

namespace MyAlgebra

Introduction "
Taking an inverse twice should return the original element.

Ex. `-(-2) = 2` or the composition of two flips is the identity.

Show that `a` is the inverse of `a⁻¹`.
"

/--
`inv_inv a` states `a = a⁻¹⁻¹`. Use it backwards to simplify a double inverse.
-/
TheoremDoc MyAlgebra.inv_inv as "inv_inv" in "Group"
@[to_additive]
Statement inv_inv {G} (a : G) [Group G] : a = a⁻¹⁻¹ := by
  apply inv_unique a⁻¹ a
  constructor
  · rw [inv_mul]
  · rw [mul_inv]

Conclusion "Congrats!"

end MyAlgebra
