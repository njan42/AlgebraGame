import Game.Levels.Group.L03_CancelRight

World "Group"
Level 4

Title "Unique Inverse"

namespace MyAlgebra

Introduction "
We proved that a monoid has only one identity. Similarly, an element of a group
has only one inverse. Show that any two-sided inverse `i` of `g` equals `g⁻¹`.
"

/--
`inv_unique` is a proof that there is only one inverse element in a group for any given element.
-/
TheoremDoc MyAlgebra.inv_unique as "inv_unique" in "Group"
@[to_additive neg_unique]
Statement inv_unique {G} (g i : G) [Group G] :
    (g * i = 1 ∧ i * g = 1) → i = g⁻¹ := by
  intro h
  rw [←mul_one g⁻¹]
  rw [←h.1]
  rw [← mul_assoc]
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats!"

end MyAlgebra
