import Game.Levels.Subgroups.L02_MulClosure

World "Subgroups"
Level 3

Title "Inverses Stay Inside"

namespace MyAlgebra

Introduction "
Closure under inverses means that `a ∈ H` implies `a⁻¹ ∈ H`.
The field `H.inv_closure` takes a membership proof and returns a proof for the inverse.

If `a` and `b` belong to `H`, what can you say about `a * b⁻¹`?
"

/-- Inverses Stay Inside. -/
TheoremDoc MyAlgebra.subgroup_mul_inv_mem as "subgroup_mul_inv_mem" in "Subgroups"
Statement subgroup_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H := by
  Hint "Which closure field handles the product? Which handles its second factor?"
  apply H.mul_closure
  · exact ha
  · exact H.inv_closure hb

/-- `H.inv_closure ha` proves membership of an inverse from its element. -/
TheoremDoc MyAlgebra.Subgroup.inv_closure as "Subgroup.inv_closure" in "Subgroups"
NewTheorem MyAlgebra.Subgroup.inv_closure

Conclusion "A subgroup is closed under products of the form `a * b⁻¹`."

end MyAlgebra
