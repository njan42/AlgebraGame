import Game.Levels.Cosets.L03_Membership

World "Cosets"
Level 4

Title "Related to Itself"

namespace MyAlgebra

Introduction "
Consider the relation on group elements defined by `a⁻¹ * b ∈ H`.
The membership test says that this is equivalent to `b ∈ aH`.

A relation is reflexive when every element is related to itself.
Does our relation have that property?
"

/-- The coset relation is reflexive. -/
TheoremDoc MyAlgebra.coset_related_refl as "coset_related_refl" in "Cosets"
Statement coset_related_refl {G : Type} [Group G] (H : Subgroup G)
    (a : G) : a⁻¹ * a ∈ H := by
  rw [inv_mul]
  exact H.one_mem

Conclusion "The relation is reflexive. We will next check symmetry and transitivity."

end MyAlgebra
