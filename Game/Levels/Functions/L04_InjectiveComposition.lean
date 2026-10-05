import Game.Levels.Functions.L03_Injective

World "Functions"
Level 4

Title "Composing Injective Functions"

namespace MyAlgebra

Introduction "
Prove that the composition of two injective functions is injective.
"

/-- The composite of two injective functions is injective. -/
TheoremDoc MyAlgebra.function_comp_injective as "function_comp_injective" in "Functions"
Statement function_comp_injective {A B C : Type} (f : A → B) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  Hint "Start with `intro a b h`."
  intro a b h
  Hint "To prove the inputs equal, use the injectivity assumptions `{hf}` and `{hg}`."
  apply hf
  apply hg
  exact h

Conclusion "An equality `g (f a) = g (f b)` first gives `f a = f b`, then `a = b`."

end MyAlgebra
