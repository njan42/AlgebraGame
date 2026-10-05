import Game.Levels.Subgroups.L08_CriterionInverse

World "Subgroups"
Level 9

Title "The Subgroup Criterion"

namespace MyAlgebra

Introduction "
Finish the shorter subgroup test by proving all three conditions of `IsSubgroupSet S`.
The previous two levels provide the identity and inverse conditions.

For multiplication, how could you express `a * b` as a product with an inverse?
The theorem `inv_inv b` reads `b = b⁻¹⁻¹`.
"

/-- The Subgroup Criterion. -/
TheoremDoc MyAlgebra.subgroup_criterion as "subgroup_criterion" in "Subgroups"
Statement subgroup_criterion {G : Type} [Group G] (S : Set G) (hne : ∃ x, x ∈ S)
    (hclose : ∀ x y, x ∈ S → y ∈ S → x * y⁻¹ ∈ S) : IsSubgroupSet S := by
  constructor
  · exact criterion_one_mem S hne hclose
  constructor
  · intro a b ha hb
    Hint "The inverse of `{b}` belongs to `{S}`. How could that help `{hclose}` produce
    the product required by the goal?"
    have hi := criterion_inv_mem S hne hclose b hb
    have h := hclose a b⁻¹ ha hi
    Hint "What does the double inverse in `{h}` simplify to?"
    rw [← inv_inv] at h
    exact h
  · intro a ha
    exact criterion_inv_mem S hne hclose a ha

Conclusion "`Subgroup.ofSet S` constructs a subgroup from the three closure proofs."

end MyAlgebra
