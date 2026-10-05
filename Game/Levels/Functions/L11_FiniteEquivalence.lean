import Game.Levels.Functions.L10_FiniteSurjective

World "Functions"
Level 11

Title "Three Ways to Say the Same Thing"

namespace MyAlgebra

Introduction "
For a function from a finite set to itself, show that injectivity, surjectivity,
and bijectivity are equivalent. We express this as two equivalences:
injectivity if and only if surjectivity, and surjectivity if and only if bijectivity.

Both assumptions matter. Adding one on `ℕ` is injective but misses `0`.
Even between finite sets, an injection from a two-element set into a three-element set
may not necessarily reach every target.
"

/-- Injectivity, surjectivity, and bijectivity are equivalent for a finite self-map. -/
TheoremDoc MyAlgebra.finite_function_equivalences as "finite_function_equivalences" in "Functions"
Statement finite_function_equivalences {S : Type} [Finite S] (f : S → S) :
    (Function.Injective f ↔ Function.Surjective f) ∧
    (Function.Surjective f ↔ Function.Bijective f) := by
  constructor
  · constructor
    · intro hf
      Hint "Which counting fact turns injectivity into surjectivity?"
      exact Finite.surjective_of_injective hf
    · intro hf
      exact finite_surjective_injective f hf
  · constructor
    · intro hf
      Hint "Bijectivity requires two properties. Which one is `{hf}`, and how can you get the other?"
      constructor
      · exact finite_surjective_injective f hf
      · exact hf
    · intro hf
      Hint "Which part of bijectivity says that every target has a preimage?"
      exact hf.2

Conclusion "Congrats! For a finite self-map, any one of these properties guarantees all three."

end MyAlgebra
