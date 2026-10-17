import Game.Levels.Lagrange.L02_Partition

World "Lagrange"
Level 3

Title "Counting Equal Pieces"

namespace MyAlgebra

Introduction "
The index, written `[G : H]`, is the number of distinct left cosets.
In Lean we'll write `H.index`.

For example, in the additive group of integers `ℤ`, the subgroup `2ℤ` of even
integers has two cosets: the even integers `2ℤ` and the odd integers `1 + 2ℤ`.
Thus `[ℤ : 2ℤ] = 2`, even though `ℤ` is infinite.
The counting formula below only considers finite groups.

The general counting theorem `card_partition` says that a finite type partitioned
into pieces of size `n` has size `(number of pieces) * n`.
It applies to any finite partition, whatever the pieces contain.

Apply that principle to the cosets. What formula relates the group size,
the subgroup size, and the index?
"

/-- The group size is the index times the subgroup size. -/
TheoremDoc MyAlgebra.lagrange_card_formula as "lagrange_card_formula" in "Lagrange"
Statement lagrange_card_formula {G : Type} [Group G] [Finite G] (H : Subgroup G)
    : Nat.card G = H.index * Nat.card H := by
  Hint "To use `card_partition`, choose the family of pieces and their common size."
  apply card_partition H.leftCosets (Nat.card H)
  · exact leftCosets_partition H
  · intro S hS
    obtain ⟨g, hg⟩ := hS
    rw [← hg]
    exact coset_card_eq H g

/-- `H.index` is the number of distinct left cosets in a finite group. -/
DefinitionDoc MyAlgebra.Subgroup.index as "Subgroup.index" in "Cosets"
/-- `card_partition parts n hp hs` counts a finite type partitioned into pieces of size `n`.
`hp` proves the partition conditions, and `hs` gives each piece's cardinality.
The conclusion is `Nat.card A = Nat.card parts * n`. -/
TheoremDoc MyAlgebra.card_partition as "card_partition" in "Counting"
NewDefinition MyAlgebra.Subgroup.index
NewTheorem MyAlgebra.card_partition

Conclusion "Count each distinct coset once, even when it has several representatives."

end MyAlgebra
