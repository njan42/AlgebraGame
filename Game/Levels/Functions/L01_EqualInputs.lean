import Game.Levels.Group

World "Functions"
Level 1

Title "Functions Respect Equality"

namespace MyAlgebra

Introduction "
The notation `f : A → B` means that `f` takes an input from `A` and returns a value in `B`.
Write `f a` to apply it to `a`. Here `A` and `B` are types: the collections of objects
we are working with. No group theory is needed for this level.

If two inputs are equal, their outputs are equal. This is the same rewriting idea
you used for multiplication, now for any function. The converse may not necessarily hold:
the constant function `fun x => 1` sends every input to the same output.
"

/-- Equal inputs give equal outputs under any function. -/
TheoremDoc MyAlgebra.function_equal_inputs as "function_equal_inputs" in "Functions"
Statement function_equal_inputs {A B : Type} (f : A → B) (a b : A) (h : a = b) :
    f a = f b := by
  Hint "Rewrite using the equality `{h}`."
  rw [h]

Conclusion "Every function respects equality. Later we will ask which functions also let us
recover equality of inputs from equality of outputs."

end MyAlgebra
