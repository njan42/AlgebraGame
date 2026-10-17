import Game.Levels.Cosets.L01_Representative

World "Cosets"
Level 2

Title "The Identity Coset"

namespace MyAlgebra

Introduction "
The representative does not have to lie in `H`, but what happens when it is `1`?

Compare membership in `H.leftCoset 1` with membership in `H.carrier`.
Does translating by the identity change the set?
"

/-- The left coset represented by the identity is the subgroup itself. -/
TheoremDoc MyAlgebra.leftCoset_one as "leftCoset_one" in "Cosets"
Statement leftCoset_one {G : Type} [Group G] (H : Subgroup G)
    : H.leftCoset 1 = H.carrier := by
  Hint "`Set.ext` reduces equality of the two sets to equivalence of their memberships."
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨h, hh, hx⟩ := hx
    rw [one_mul] at hx
    rw [hx]
    exact hh
  · intro hx
    Hint "Which element of `{H}` produces `{x}` when multiplied by the identity?"
    use x
    constructor
    · exact hx
    · rw [one_mul]

Conclusion "The subgroup itself is the coset with representative `1`."

end MyAlgebra
