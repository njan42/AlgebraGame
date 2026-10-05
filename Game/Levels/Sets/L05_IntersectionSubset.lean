import Game.Levels.Sets.L04_Intersection

World "Sets"
Level 5

Title "An Intersection Lies Inside Each Set"

namespace MyAlgebra

Introduction "
How does belonging to both `S` and `T` compare with belonging to `S`?
Prove that `S ∩ T ⊆ S`.
"

/-- The intersection of two sets is contained in the first set. -/
TheoremDoc MyAlgebra.set_intersection_subset as "set_intersection_subset" in "Sets"
Statement set_intersection_subset {A : Type} (S T : Set A) : S ∩ T ⊆ S := by
  intro x hx
  Hint "The hypothesis `{hx}` contains two membership proofs. Which one does the goal ask for?"
  exact hx.1

Conclusion "Proving inclusion means working with an arbitrary element.
You do not need to enumerate a set, even when it is infinite."

end MyAlgebra
