import Game.Levels.Group.L02_CancelLeft

World "Group"
Level 3

Title "Cancel Right Multiplication"

namespace MyAlgebra

Introduction "
Now prove cancellation of a common factor on the right.
Which side should you multiply by its inverse?
"

/--
`mul_right_cancel g` cancels a common right factor `g` from an equality.
-/
TheoremDoc MyAlgebra.mul_right_cancel as "mul_right_cancel" in "Group"
@[to_additive]
Statement mul_right_cancel {G} (g : G) {g1 g2 : G} [Group G] : g1 * g = g2 * g → g1 = g2 := by
  intro h
  Hint "What could you multiply both sides by to remove the common right factor?"
  have q := mul_right (g⁻¹) h
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_one] at q
  rw [mul_one] at q
  exact q

Conclusion "Congrats!"

end MyAlgebra
