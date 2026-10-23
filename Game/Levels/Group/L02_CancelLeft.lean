import Game.Levels.Group.L01_MulInv

World "Group"
Level 2

Title "Cancel Left Multiplication"

namespace MyAlgebra

Introduction "
In Monoid, equal elements stayed equal after multiplication on the left.
In a group, can we reverse that argument and cancel a common left factor?
"

/--
`mul_left_cancel g` cancels a common left factor `g` from an equality.
-/
TheoremDoc MyAlgebra.mul_left_cancel as "mul_left_cancel" in "Group"
@[to_additive]
Statement mul_left_cancel {G} (g : G) {g1 g2 : G} [Group G] : g * g1 = g * g2 → g1 = g2 := by
  intro h
  Hint "What can we do to get rid of the `g` on both sides? It might help to use a previous lemma."
  have q := mul_left g⁻¹ h
  Hint "Reassociate the products in `{q}` so that `{g}⁻¹` and `{g}` meet."
  rw [←mul_assoc] at q
  rw [←mul_assoc] at q
  rw [inv_mul] at q
  rw [one_mul] at q
  rw [one_mul] at q
  exact q

Conclusion "Congrats!"

NewTheorem MyAlgebra.Group.mul_inv

end MyAlgebra
