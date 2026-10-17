import Game.Levels.Cosets.L05_Symmetric

World "Cosets"
Level 6

Title "Following the Relation"

namespace MyAlgebra

Introduction "
A relation is transitive when relating `a` to `b` and `b` to `c` also relates `a` to `c`.

What happens when you multiply `a⁻¹ * b` by `b⁻¹ * c`?
Which adjacent factors can cancel?
"

/-- The coset relation is transitive. -/
TheoremDoc MyAlgebra.coset_related_trans as "coset_related_trans" in "Cosets"
Statement coset_related_trans {G : Type} [Group G] (H : Subgroup G)
    (a b c : G)
    (hab : a⁻¹ * b ∈ H) (hbc : b⁻¹ * c ∈ H) : a⁻¹ * c ∈ H := by
  have h := H.mul_closure hab hbc
  Hint "Reassociate the product in `{h}` so that `{b}` and `{b}⁻¹ meet.
  Giving `mul_assoc` its three factors chooses which product to regroup."
  rw [mul_assoc, ← mul_assoc b b⁻¹ c, mul_inv, one_mul] at h
  exact h

Conclusion "The relation is reflexive, symmetric, and transitive: it is an equivalence relation.
The corresponding classes will be our cosets."

end MyAlgebra
