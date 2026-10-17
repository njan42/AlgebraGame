import Game.Levels.Subgroups
import Game.MyAlgebra.Coset_Def

World "Cosets"
Level 1

Title "A Coset Contains Its Representative"

namespace MyAlgebra

Introduction "
The left coset `gH` is the set you get by multiplying every element of `H` on the left by `g`.
We'll write it in Lean as `H.leftCoset g`. Membership means
`x ∈ H.leftCoset g ↔ ∃ h, h ∈ H ∧ x = g * h`.
The element `g` is called a representative of the coset.

Does `g` itself belong to `gH`? Which element of `H` could produce it?
"

/-- The representative of a left coset belongs to that coset. -/
TheoremDoc MyAlgebra.mem_own_leftCoset as "mem_own_leftCoset" in "Cosets"
Statement mem_own_leftCoset {G : Type} [Group G] (H : Subgroup G)
    (g : G) : g ∈ H.leftCoset g := by
  Hint "Give an element of `{H}` whose product with `{g}` is `{g}`."
  use 1
  constructor
  · exact H.one_mem
  · rw [mul_one]

/-- `H.leftCoset g` is `{x | ∃ h, h ∈ H ∧ x = g * h}`. -/
DefinitionDoc MyAlgebra.Subgroup.leftCoset as "Subgroup.leftCoset" in "Cosets"
NewDefinition MyAlgebra.Subgroup.leftCoset

Conclusion "Every coset contains its representative, so every group element belongs to a coset."

end MyAlgebra
