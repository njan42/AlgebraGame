import Game.Levels.Sets.L03_SubsetTransitive

World "Sets"
Level 4

Title "Belonging to Both Sets"

namespace MyAlgebra

Introduction "
The intersection `S ∩ T` consists of the elements belonging to both sets.
Type `∩` with `\\cap`. Membership in an intersection means a conjunction:
`x ∈ S ∩ T` means `x ∈ S ∧ x ∈ T`.
"

/-- An element of each of two sets belongs to their intersection. -/
TheoremDoc MyAlgebra.set_mem_intersection as "set_mem_intersection" in "Sets"
Statement set_mem_intersection {A : Type} (S T : Set A) (x : A)
    (hS : x ∈ S) (hT : x ∈ T) : x ∈ S ∩ T := by
  Hint "Split membership in the intersection into two goals with `constructor`."
  constructor
  · exact hS
  · exact hT

/-- `S ∩ T` is the intersection: `x ∈ S ∩ T` means `x ∈ S ∧ x ∈ T`.
Use `constructor` to prove both memberships; use `h.1` and `h.2` to extract them. -/
DefinitionDoc Set.inter as "Set.inter" in "Sets"

NewDefinition Set.inter

Conclusion "An element belongs to an intersection exactly when it belongs to both sets."

end MyAlgebra
