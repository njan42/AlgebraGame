import Game.Levels.Normal.L04_Kernel

World "Normal"
Level 5

Title "From a Left Coset to a Right Coset"

namespace MyAlgebra

Introduction "
A left coset `gN` has elements `g * n`. A right coset `Ng` has elements `n * g`.
In Lean we write the right coset as `N.rightCoset g`, with membership
`x ∈ N.rightCoset g ↔ ∃ n, n ∈ N ∧ x = n * g`.

For a normal subgroup, can you express an element `g * n` as `m * g`
for some `m ∈ N`, even without commutativity of the group?
"

/-- A normal subgroup has each left coset contained in the corresponding right coset. -/
TheoremDoc MyAlgebra.normal_leftCoset_subset_rightCoset as "normal_leftCoset_subset_rightCoset"
  in "Normal Subgroups"
Statement normal_leftCoset_subset_rightCoset {G : Type} [Group G] (N : Subgroup G)
    (hN : N.IsNormal) (g : G) : N.leftCoset g ⊆ N.rightCoset g := by
  intro x hx
  obtain ⟨n, hn, hx⟩ := hx
  Hint "Use the conjugate `{g} * {n} * {g}⁻¹` as the right-coset witness."
  use g * n * g⁻¹
  constructor
  · exact hN g n hn
  · rw [hx, mul_assoc, inv_mul, mul_one]

/-- `N.rightCoset g` is `{x | ∃ n, n ∈ N ∧ x = n * g}`. -/
DefinitionDoc MyAlgebra.Subgroup.rightCoset as "Subgroup.rightCoset" in "Cosets"
NewDefinition MyAlgebra.Subgroup.rightCoset

Conclusion "For a normal subgroup, every left coset is contained in the corresponding right coset.
Normality supplies a new subgroup element; it does not require the factors to commute."

end MyAlgebra
