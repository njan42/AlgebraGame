import Game.Levels.Subgroups.L01_Nonempty

World "Subgroups"
Level 2

Title "Multiplication Stays Inside"

namespace MyAlgebra

Introduction "
Closure under multiplication means that multiplying two elements of `H` stays in `H`.
The field `H.mul_closure` takes proofs of those two memberships.

Suppose three elements belong to `H`. Does their product still belong to `H`?
"

/-- Multiplication Stays Inside. -/
TheoremDoc MyAlgebra.subgroup_mul_three as "subgroup_mul_three" in "Subgroups"
Statement subgroup_mul_three {G : Type} [Group G] (H : Subgroup G) (a b c : G)
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) : (a * b) * c ∈ H := by
  Hint "The field `{H}.mul_closure` proves that a product belongs to the subgroup.
  Which two memberships does the outer product require?"
  apply H.mul_closure
  · exact H.mul_closure ha hb
  · exact hc

/-- `H.mul_closure ha hb` proves membership of a product from its factors. -/
TheoremDoc MyAlgebra.Subgroup.mul_closure as "Subgroup.mul_closure" in "Subgroups"
NewTheorem MyAlgebra.Subgroup.mul_closure

Conclusion "Repeated multiplication stays inside a subgroup."

end MyAlgebra
