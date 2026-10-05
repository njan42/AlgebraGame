import Game.Levels.Functions.L05_Surjective

World "Functions"
Level 6

Title "Following Preimages Backwards"

namespace MyAlgebra

Introduction "
You have proved that composing injective functions preserves injectivity.
Does composing two surjective functions also reach every element of the final target?

"

/-- The composite of two surjective functions is surjective. -/
TheoremDoc MyAlgebra.function_comp_surjective as "function_comp_surjective" in "Functions"
Statement function_comp_surjective {A B C : Type} (f : A → B) (g : B → C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  intro c
  Hint "Which surjectivity assumption gives a preimage of `{c}` under the outer function?"
  obtain ⟨b, hb⟩ := hg c
  Hint "Now find a preimage of `{b}` under `{f}` using `{hf}`."
  obtain ⟨a, ha⟩ := hf b
  use a
  change g (f a) = c
  rw [ha]
  exact hb

Conclusion "The composition of two surjective functions is surjective."

end MyAlgebra
