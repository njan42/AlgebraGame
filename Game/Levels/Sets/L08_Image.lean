import Game.Levels.Sets.L07_Preimage

World "Sets"
Level 8

Title "An Image Needs a Witness"

namespace MyAlgebra

Introduction "
The image `f '' S` consists of outputs reached by inputs in `S`. Use two ordinary apostrophes.
Membership `y ∈ f '' S` means `∃ x, x ∈ S ∧ f x = y`.

To prove membership, supply an input, a proof that it belongs to `S`, and an equation
showing it maps to the desired output.
"

/-- The value at an input in a set belongs to the image of that set. -/
TheoremDoc MyAlgebra.set_mem_image as "set_mem_image" in "Sets"
Statement set_mem_image {A B : Type} (f : A → B) (S : Set A)
    (a : A) (ha : a ∈ S) : f a ∈ f '' S := by
  Hint "Which input produces this output? You also need its membership proof and output equation."
  exact ⟨a, ha, rfl⟩

/-- `f '' S` is the image of `S` under `f`.
Membership is `∃ x, x ∈ S ∧ f x = y`; prove it by giving a witness and both proofs. -/
DefinitionDoc Set.image as "Set.image" in "Sets"

NewDefinition Set.image

Conclusion "The image of a homomorphism will give us an example of a subgroup."

end MyAlgebra
