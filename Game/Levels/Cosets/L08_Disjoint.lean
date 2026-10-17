import Game.Levels.Cosets.L07_CommonElement

World "Cosets"
Level 8

Title "Distinct Cosets Do Not Overlap"

namespace MyAlgebra

Introduction "
Two sets are disjoint when they have no element in common. Lean writes `Disjoint S T`.
The theorem `Set.disjoint_left` expresses this as
`∀ x, x ∈ S → x ∈ T → False`.

Here `hne : S ≠ T` rules out equality: applying `hne` to a proof of `S = T` gives `False`.
If two distinct cosets shared an element, what would the previous level imply?
"

/-- Distinct left cosets of the same subgroup are disjoint. -/
TheoremDoc MyAlgebra.leftCoset_disjoint_of_ne as "leftCoset_disjoint_of_ne" in "Cosets"
Statement leftCoset_disjoint_of_ne {G : Type} [Group G] (H : Subgroup G)
    (a b : G) (hne : H.leftCoset a ≠ H.leftCoset b) :
    Disjoint (H.leftCoset a) (H.leftCoset b) := by
  Hint "`Set.disjoint_left.mpr` reduces disjointness to showing
  that no element can belong to both sets."
  apply Set.disjoint_left.mpr
  intro x hax hbx
  exact hne (leftCoset_eq_of_common H a b x hax hbx)

/-- `Disjoint S T` means the sets have no common element. -/
DefinitionDoc Disjoint as "Disjoint" in "Sets"
/-- `Set.disjoint_left` converts set disjointness to `∀ x, x ∈ S → x ∈ T → False`. -/
TheoremDoc Set.disjoint_left as "Set.disjoint_left" in "Sets"
NewDefinition Disjoint
NewTheorem Set.disjoint_left

Conclusion "Cosets cover the group without overlapping: every element lies in one coset,
and any two cosets are either equal or disjoint. This is a partition of the group."

end MyAlgebra
