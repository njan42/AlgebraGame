import Game.Levels.Sets.L05_IntersectionSubset

World "Sets"
Level 6

Title "Same Elements, Same Set"

namespace MyAlgebra

Introduction "
Two sets are equal when they have exactly the same elements. The theorem `Set.ext`
turns a goal `S = T` into `∀ x, x ∈ S ↔ x ∈ T`.

Does the order of the two sets affect which elements belong to their intersection?
Prove `S ∩ T = T ∩ S`.

Angle brackets can construct a conjunction:
if `hP : P` and `hQ : Q`, then `⟨hP, hQ⟩` is a proof of `P ∧ Q`.
"

/-- Interchanging the two sets does not change their intersection. -/
TheoremDoc MyAlgebra.set_intersection_comm as "set_intersection_comm" in "Sets"
Statement set_intersection_comm {A : Type} (S T : Set A) : S ∩ T = T ∩ S := by
  Hint "`Set.ext` reduces set equality to comparing membership of an arbitrary element."
  apply Set.ext
  intro x
  constructor
  · intro hx
    Hint "The required memberships are the two parts of `{hx}`, in the opposite order."
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-- `Set.ext` proves two sets equal from `∀ x, x ∈ S ↔ x ∈ T`.
Use `apply Set.ext`, `intro x`, then prove the two directions of membership. -/
TheoremDoc Set.ext as "Set.ext" in "Sets"

NewTheorem Set.ext

Conclusion "Two sets with the same elements are equal."

end MyAlgebra
