import Game.Levels.Subgroups.L07_CriterionIdentity

World "Subgroups"
Level 8

Title "A Shorter Test: Inverses"

namespace MyAlgebra

Introduction "
You have shown that the shorter test forces the identity to belong to `S`.

What happens to `x * y⁻¹` when `x` is the identity?
Prove that every element of `S` has its inverse in `S`.
"

/-- A Shorter Test: Inverses. -/
TheoremDoc MyAlgebra.criterion_inv_mem as "criterion_inv_mem" in "Subgroups"
Statement criterion_inv_mem {G : Type} [Group G] (S : Set G) (hne : ∃ x, x ∈ S)
    (hclose : ∀ x y, x ∈ S → y ∈ S → x * y⁻¹ ∈ S)
    (a : G) (ha : a ∈ S) : a⁻¹ ∈ S := by
  Hint "Use `criterion_one_mem` from the previous level to obtain membership of `1`."
  have h1 := criterion_one_mem S hne hclose
  have h := hclose 1 a h1 ha
  rw [one_mul] at h
  exact h

Conclusion "Containing the identity and being closed under multiplication alone is not enough.
What about inverses?"

end MyAlgebra
