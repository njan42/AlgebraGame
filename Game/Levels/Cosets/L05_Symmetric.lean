import Game.Levels.Cosets.L04_Reflexive

World "Cosets"
Level 5

Title "Reversing the Relation"

namespace MyAlgebra

Introduction "
A relation is symmetric when relating `a` to `b` also relates `b` to `a`.

If `a⁻¹ * b` belongs to `H`, what can you say about its inverse?
How does that inverse compare with `b⁻¹ * a`?
"

/-- The coset relation is symmetric. -/
TheoremDoc MyAlgebra.coset_related_symm as "coset_related_symm" in "Cosets"
Statement coset_related_symm {G : Type} [Group G] (H : Subgroup G)
    (a b : G) (hab : a⁻¹ * b ∈ H) : b⁻¹ * a ∈ H := by
  have h := H.inv_closure hab
  Hint "What happens to the order of the factors when you invert the product in `{h}`?
  Check whether any double inverses remain."
  rw [← inv_anticomm, ← inv_inv] at h
  exact h

Conclusion "Reversing the relation stays within the subgroup because it is closed under inverses."

end MyAlgebra
