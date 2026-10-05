import Game.Levels.Sets.L01_Membership

World "Sets"
Level 2

Title "Using an Inclusion"

namespace MyAlgebra

Introduction "
The notation `S ⊆ T` means every element of `S` also belongs to `T`.
Type `⊆` with `\\subseteq`. In Lean this means `∀ x, x ∈ S → x ∈ T`,
with the element `x` supplied implicitly when we apply the inclusion.

Thus a hypothesis `hST : S ⊆ T` acts like a function on membership proofs:
if `hx : x ∈ S`, then `hST hx` proves `x ∈ T`.
"

/-- An inclusion transfers membership from the smaller set to the larger set. -/
TheoremDoc MyAlgebra.set_subset_apply as "set_subset_apply" in "Sets"
Statement set_subset_apply {A : Type} (S T : Set A) (hST : S ⊆ T)
    (x : A) (hx : x ∈ S) : x ∈ T := by
  Hint "What does the inclusion `{hST}` tell you about an element satisfying `{hx}`?"
  exact hST hx

/-- `S ⊆ T` means `∀ ⦃x⦄, x ∈ S → x ∈ T`.
To use `hST : S ⊆ T`, apply it to a proof of membership in `S`.
To prove an inclusion, start with `intro x hx`. -/
DefinitionDoc Set.Subset as "Set.Subset" in "Sets"

NewDefinition Set.Subset

Conclusion "Set inclusion is an implication about membership.
An element of `T` may not necessarily lie in `S`: inclusion only gives one direction."

end MyAlgebra
