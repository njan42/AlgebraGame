import Game.Levels.Lagrange.L01_CosetSize

World "Lagrange"
Level 2

Title "The Pieces Cover the Group"

namespace MyAlgebra

Introduction "
`H.leftCosets` is the set of distinct left cosets. A set `S` belongs to it
when `∃ g, H.leftCoset g = S`. Representatives that describe the same coset
contribute just one set.

`IsPartition parts` has three conditions: each piece is nonempty, every element
belongs to a piece, and pieces sharing an element are equal.
For a set `S`, `S.Nonempty` means `∃ x, x ∈ S`.

Do the coset results establish all three conditions?
"

/-- The distinct left cosets form a partition of the group. -/
TheoremDoc MyAlgebra.leftCosets_partition as "leftCosets_partition" in "Lagrange"
Statement leftCosets_partition {G : Type} [Group G] [Finite G] (H : Subgroup G)
    : IsPartition H.leftCosets := by
  constructor
  · intro S hS
    obtain ⟨g, hg⟩ := hS
    rw [← hg]
    exact ⟨g, mem_own_leftCoset H g⟩
  constructor
  · intro x
    Hint "Choose the coset represented by `{x}`. Show it is a coset and contains `{x}`."
    use H.leftCoset x
    constructor
    · exact ⟨x, rfl⟩
    · exact mem_own_leftCoset H x
  · intro S hS T hT x hx hy
    obtain ⟨a, ha⟩ := hS
    obtain ⟨b, hb⟩ := hT
    Hint "Rewrite the sets as cosets, then use the shared element `{x}`."
    rw [← ha] at hx
    rw [← hb] at hy
    rw [← ha, ← hb]
    exact leftCoset_eq_of_common H a b x hx hy

/-- `H.leftCosets` consists of distinct sets `H.leftCoset g`. -/
DefinitionDoc MyAlgebra.Subgroup.leftCosets as "Subgroup.leftCosets" in "Cosets"
/-- A partition has nonempty pieces, covers every element,
and has no overlapping distinct pieces. -/
DefinitionDoc MyAlgebra.IsPartition as "IsPartition" in "Counting"
/-- `S.Nonempty` means `∃ x, x ∈ S`. -/
DefinitionDoc Set.Nonempty as "Set.Nonempty" in "Sets"
NewDefinition MyAlgebra.Subgroup.leftCosets MyAlgebra.IsPartition Set.Nonempty

Conclusion "Each group element belongs to exactly one distinct left coset.
We can count the group by counting those pieces."

end MyAlgebra
