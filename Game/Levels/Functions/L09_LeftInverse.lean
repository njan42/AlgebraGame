import Game.Levels.Functions.L08_InverseBijection

World "Functions"
Level 9

Title "Undoing a Function"

namespace MyAlgebra

Introduction "
Suppose `f : A → B` and `s : B → A` satisfy `s (f x) = x` for every input.
Then `s` is a **left inverse** of `f` i.e. applying `s` undoes `f`.
For example, multiplying by `g⁻¹` on the left undoes multiplying by `g`.

Can two different inputs have the same output if we can undo the function?
"

/-- A function with a left inverse is injective. -/
TheoremDoc MyAlgebra.left_inverse_injective as "left_inverse_injective" in "Functions"
Statement left_inverse_injective {A B : Type} (f : A → B) (s : B → A)
    (hs : ∀ x, s (f x) = x) : Function.Injective f := by
  intro a b h
  Hint "What happens when you undo the equal outputs? Use `{hs}` to relate each
  input to its recovered value."
  calc
    a = s (f a) := by rw [hs]
    _ = s (f b) := by rw [h]
    _ = b := hs b

Conclusion "Congrats!"

end MyAlgebra
