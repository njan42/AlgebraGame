import Game.Levels.Functions.L09_LeftInverse
import Game.MyAlgebra.FiniteFunctions

World "Functions"
Level 10

Title "No Room for Repeated Outputs"

namespace MyAlgebra

Introduction "
The assumption `[Finite S]` says that `S` has finitely many elements.
We will study functions `f : S → S`, whose input and target are the same finite set.

The pigeonhole principle gives a counting fact: an injective function `S → S`
must reach every target. Distinct inputs already account for all the available outputs.
Mathlib calls this `Finite.surjective_of_injective`.

Now prove the converse. Suppose `f` is surjective. We can choose a preimage `s y`
for each target `y`, giving `f (s y) = y`. This makes `s` a **right inverse** of `f`.
A left inverse satisfies the equation `s (f x) = x`.

Use the counting fact to show that this right inverse is also a left inverse.
"

/-- A surjective function from a finite set to itself is injective. -/
TheoremDoc MyAlgebra.finite_surjective_injective as "finite_surjective_injective" in "Functions"
Statement finite_surjective_injective {S : Type} [Finite S] (f : S → S) :
    Function.Surjective f → Function.Injective f := by
  intro hf
  Hint "The rule `choose_preimages` supplies a function choosing one preimage per target,
  together with its output equation."
  obtain ⟨s, hs⟩ := choose_preimages f hf
  Hint "The equation `{hs}` says that `{f}` undoes `{s}`. What does this tell you about `{s}`?"
  have hsi := left_inverse_injective s f hs
  Hint "`Finite.surjective_of_injective` turns injectivity of a finite self-map into
  surjectivity. Does `{s}` therefore reach every input of `{f}`?"
  have hss := Finite.surjective_of_injective hsi
  have hleft : ∀ x, s (f x) = x := by
    intro x
    Hint "Since `{s}` is surjective, write `{x}` as one of its outputs.
    How does `{hs}` simplify the resulting expression?"
    obtain ⟨y, hy⟩ := hss x
    rw [← hy, hs]
  Hint "You now have an equation saying that `{s}` undoes `{f}`. What follows about `{f}`?"
  exact left_inverse_injective f s hleft

/-- `Finite S` says that the type `S` has finitely many elements. -/
DefinitionDoc Finite as "Finite" in "Counting"
/-- For an injective function `f : S → S` with `[Finite S]`,
`Finite.surjective_of_injective hf` proves surjectivity.
This is the finite pigeonhole principle. -/
TheoremDoc Finite.surjective_of_injective as "Finite.surjective_of_injective" in "Functions"
/-- For a surjective `f : A → B`, `choose_preimages f hf` gives
`∃ s : B → A, ∀ y, f (s y) = y`: choose one preimage for every target.
This does not assert that the chosen function is a left inverse. -/
TheoremDoc MyAlgebra.choose_preimages as "choose_preimages" in "Functions"
NewDefinition Finite
NewTheorem Finite.surjective_of_injective MyAlgebra.choose_preimages

Conclusion "Congrats! On a finite set, a self-map cannot reach every target and repeat an output."

end MyAlgebra
