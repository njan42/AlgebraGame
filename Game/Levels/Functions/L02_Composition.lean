import Game.Levels.Functions.L01_EqualInputs

World "Functions"
Level 2

Title "One Function After Another"

namespace MyAlgebra

Introduction "
Suppose `f : A → B` and `g : B → C`. The composite `g ∘ f` first applies `f`, then `g`.
Type `∘` with `\\circ`. The order matters here.

For example, if `f` adds one and `g` doubles a natural number, `(g ∘ f) 3` is 8,
while `(f ∘ g) 3` is 7.

Composition is defined by `(g ∘ f) a = g (f a)`, so `rfl` proves this equality.
The tactic `change` can also display a definition in an expanded form without changing
the meaning of the goal.
"

/-- A composite applies the right-hand function first. -/
TheoremDoc MyAlgebra.function_comp_apply as "function_comp_apply" in "Functions"
Statement function_comp_apply {A B C : Type} (f : A → B) (g : B → C) (a : A) :
    (g ∘ f) a = g (f a) := by
  Hint "Expand using `change`, or finish directly with `rfl`."
  change g (f a) = g (f a)
  rfl

/-- `(g ∘ f) a` means `g (f a)`. Type `∘` with `\circ`. -/
DefinitionDoc Function.comp as "Function.comp" in "Functions"

/-- `change new_goal` replaces the goal with an expression equal by definition.
For example, expand `(g ∘ f) a` to `g (f a)`. It does not use an algebraic theorem.
Use `change new_type at h` to expand a definition in a hypothesis. -/
TacticDoc change

NewDefinition Function.comp
NewTactic change

Conclusion "Function composition applies the inner function first, then the outer function."

end MyAlgebra
