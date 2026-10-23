import Game.Levels.Group.L08_InvInv

World "Group"
Level 9

Title "Inverse is Injective"

namespace MyAlgebra

Introduction "
If two elements have the same inverse, can the original elements be different?
Prove both directions of the equivalence.
"

/--
`inv_inj` is a proof that the inverse is injective.
-/
TheoremDoc MyAlgebra.inv_inj as "inv_inj" in "Group"
@[to_additive]
Statement inv_inj {G} (a b : G) [Group G] : a⁻¹ = b⁻¹ ↔ a = b := by
  constructor
  · intro h
    calc
      a = a⁻¹⁻¹ := inv_inv a
      _ = b⁻¹⁻¹ := by rw [h]
      _ = b := by rw [← inv_inv]
  · intro h
    rw [h]

Conclusion "Congrats!"

end MyAlgebra
