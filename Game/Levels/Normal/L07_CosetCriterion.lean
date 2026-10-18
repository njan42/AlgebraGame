import Game.Levels.Normal.L06_CosetEquality

World "Normal"
Level 7

Title "A Coset Test for Normality"

namespace MyAlgebra

Introduction "
What about the reverse direction?

Suppose the left and right cosets of a subgroup agree for every representative.
Does this force the subgroup to be normal?

For `n ∈ N`, which coset contains `g * n`?
What does membership in the other coset tell you about its conjugate?
"

/-- Equality of all corresponding left and right cosets implies normality. -/
TheoremDoc MyAlgebra.isNormal_of_coset_eq as "isNormal_of_coset_eq" in "Normal Subgroups"
Statement isNormal_of_coset_eq {G : Type} [Group G] (N : Subgroup G)
    (hcosets : ∀ g, N.leftCoset g = N.rightCoset g) : N.IsNormal := by
  intro g n hn
  have hx : g * n ∈ N.leftCoset g := ⟨n, hn, rfl⟩
  rw [hcosets g] at hx
  obtain ⟨m, hm, hprod⟩ := hx
  Hint "Replace `{g} * {n}` using `{hprod}`, then cancel the adjacent inverse factors."
  rw [hprod, mul_assoc, mul_inv, mul_one]
  exact hm

Conclusion "A subgroup is normal exactly when all its left and right cosets agree.
You can now use either conjugation or coset equality to prove normality."

end MyAlgebra
