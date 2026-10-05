import Game.Levels.Sets.L02_Subset

World "Sets"
Level 3

Title "Chaining Inclusions"

namespace MyAlgebra

Introduction "
If `S ⊆ T` and `T ⊆ U`, then `S ⊆ U`.
Take an arbitrary element `x` of `S`, move it into `T`, and then into `U`.

An inclusion is proved with `intro x hx`, just as a function property is proved
by introducing its inputs and assumptions.
"

/-- Set inclusion is transitive. -/
TheoremDoc MyAlgebra.set_subset_transitive as "set_subset_transitive" in "Sets"
Statement set_subset_transitive {A : Type} (S T U : Set A)
    (hST : S ⊆ T) (hTU : T ⊆ U) : S ⊆ U := by
  intro x hx
  Hint "Use `{hTU}` to reduce the goal to membership in the middle set."
  apply hTU
  exact hST hx

Conclusion "Set inclusion is transitive."

end MyAlgebra
