import Game.Levels.Subgroups.L06_Intersection

World "Subgroups"
Level 7

Title "A Shorter Test: Identity"

namespace MyAlgebra

Introduction "
There is a shorter subgroup test: a set is nonempty and is closed under `x * y⁻¹`.
Here `hne` supplies an element of `S`, and `hclose` expresses that closure condition.

What happens when the two inputs to this operation are equal?
Use the hypotheses to show that `S` contains the identity.
"

/-- A Shorter Test: Identity. -/
TheoremDoc MyAlgebra.criterion_one_mem as "criterion_one_mem" in "Subgroups"
Statement criterion_one_mem {G : Type} [Group G] (S : Set G) (hne : ∃ x, x ∈ S)
    (hclose : ∀ x y, x ∈ S → y ∈ S → x * y⁻¹ ∈ S) : 1 ∈ S := by
  Hint "Unpack `{hne}` with `obtain` to get an element and its membership."
  obtain ⟨s, hs⟩ := hne
  Hint "Which two elements could you give `{hclose}` so that their product simplifies to `1`?"
  have h := hclose s s hs hs
  rw [mul_inv] at h
  exact h

Conclusion "The empty set satisfies the closure condition, so nonemptiness is a necessary assumption."

end MyAlgebra
