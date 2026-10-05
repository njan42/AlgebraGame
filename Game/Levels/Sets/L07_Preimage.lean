import Game.Levels.Sets.L06_SetEquality

World "Sets"
Level 7

Title "Pulling a Set Back Along a Function"

namespace MyAlgebra

Introduction "
The preimage `f ⁻¹' S` consists of all inputs whose outputs lie in `S`:
`x ∈ f ⁻¹' S` means `f x ∈ S`. Type `⁻¹` with `\\inv` and then add the apostrophe.
This notation does not require an inverse function; every function has preimages of sets.

If we enlarge a set of outputs from `S` to `T`, what happens to the inputs whose
outputs lie in that set? Show that taking preimages preserves inclusion.
"

/-- Taking preimages preserves inclusion. -/
TheoremDoc MyAlgebra.set_preimage_subset as "set_preimage_subset" in "Sets"
Statement set_preimage_subset {A B : Type} (f : A → B) (S T : Set B)
    (hST : S ⊆ T) : f ⁻¹' S ⊆ f ⁻¹' T := by
  intro x hx
  Hint "Express preimage membership using the output `{f} {x}`."
  change f x ∈ S at hx
  change f x ∈ T
  Hint "How does the inclusion `{hST}` relate the two output memberships?"
  exact hST hx

/-- `f ⁻¹' S` is the preimage `{x | f x ∈ S}`.
It is a set of inputs and exists for every function, whether or not it is bijective. -/
DefinitionDoc Set.preimage as "Set.preimage" in "Sets"

NewDefinition Set.preimage

Conclusion "For a group homomorphism, the inputs sent to the identity form its kernel.
That is a preimage of a set containing just the identity."

end MyAlgebra
